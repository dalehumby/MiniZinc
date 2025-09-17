% ===============================
% Production-ish battery dispatcher + pool pump (refactored)
% Rolling horizon, MPC-friendly
% ===============================

% ---------- Units legend ----------
% kW  : power
% kWh : energy
% currency/kWh : prices & per-kWh penalties
% 0/1 : booleans (encoded as int 0..1)
% ----------------------------------

% --------- Sets & horizon ----------
int: T;                                 % e.g., 36 or 48
set of int: H = 1..T;

% Time mapping: index -> hour-of-day & day index
int: start_hour_of_day;                 % hour-of-day at t=1 (0..23)
function int: hour_of_day(int: t) = (start_hour_of_day + (t - 1)) mod 24;
function int: day_index(int: t)   = (start_hour_of_day + (t - 1)) div 24;

% --------- Inputs (data) ----------
% Forecasts (per hour)
array[H] of float: solar_gen_kw;        % PV generation (kW)
array[H] of float: base_load_kw;        % house base load, excludes controllables (kW)
array[H] of float: price_buy_per_kwh;   % import price (currency/kWh)
array[H] of float: price_sell_per_kwh;  % feed-in tariff (currency/kWh)
array[H] of int: grid_outage_on;        % 1 = grid OFF, 0 = normal

% Battery & grid
float: batt_capacity_kwh;               % battery capacity (kWh)
float: batt_power_max_kw;               % max charge/discharge power (kW)
float: eff_charge;                      % charge efficiency (0..1)
float: eff_discharge;                   % discharge efficiency (0..1)
float: soc0_kwh;                        % initial state of charge at t=1 (kWh)
float: soc_min_kwh;                     % minimum SOC (kWh)
float: soc_max_kwh;                     % maximum SOC (kWh) (= capacity)

float: grid_import_max_kw;              % interconnect import limit (kW)
float: grid_export_max_kw;              % interconnect export limit (kW)

% Costs / penalties
float: pen_batt_wear_per_kwh;           % linear throughput proxy (currency/kWh)
float: pen_terminal_soc_per_kwh;        % end-of-horizon SOC band penalty (currency/kWh)
float: pen_mode_switch_per_event;       % discourage mode flips (currency/switch)
float: pen_export_per_kwh;              % optional export penalty (currency/kWh)

% Terminal SOC preference (soft band)
float: soc_target_min_kwh;              % desired min at t=T (kWh)
float: soc_target_max_kwh;              % desired max at t=T (kWh)

% Advice heuristics
float: cheap_marginal_cost_threshold_per_kwh;
float: export_surplus_threshold_kw;
float: pen_advice_discharge_nudge_per_kwh;

% Pool pump parameters
float: pump_power_kw;                   % power when ON (kW)
int:   pump_run_hours_min_per_day;      % e.g., 6 hours/day
int:   pump_window_start_hod;           % earliest start (08:00 inclusive)
int:   pump_window_end_hod;             % latest end (20:00 exclusive)
int:   pump_hours_done_today;           % hours already run today before t=1
float: pen_pump_shortage_per_hour;      % penalty for unmet hours today

% Pre load-shedding anchor
float: pre_shed_soc_min_kwh;            % e.g., 3.0
float: pen_pre_shed_soc_per_kwh;        % e.g., 0.05 (gentle nudge)

% Cap for pv_used_kw domain = max PV seen in the horizon
float: pv_used_cap_kw = max([ solar_gen_kw[t] | t in H ]);

% --------- Decision variables ----------
array[H] of var 0.0..grid_import_max_kw: grid_import_kw;
array[H] of var 0.0..grid_export_max_kw: grid_export_kw;
array[H] of var 0.0..batt_power_max_kw:  batt_charge_kw;
array[H] of var 0.0..batt_power_max_kw:  batt_discharge_kw;
array[H] of var soc_min_kwh..soc_max_kwh: soc_kwh;

% Battery mode: 1 = discharging, 0 = charging (prevents simultaneous c & d)
array[H] of var 0..1: is_discharging;

% Pool pump on/off
array[H] of var 0..1: pump_is_on;

% PV actually taken onto the AC bus (kW). The remainder is spilled.
array[H] of var 0.0..pv_used_cap_kw: pv_used_kw;

% Terminal SOC band slacks (tight bounds = capacity)
var 0.0..batt_capacity_kwh: terminal_soc_shortfall_kwh;   % below soc_target_min_kwh
var 0.0..batt_capacity_kwh: terminal_soc_excess_kwh;      % above soc_target_max_kwh

% Mode switching helper: |is_discharging[t] - is_discharging[t-1]|
array[2..T] of var 0.0..1.0: mode_change;


% --------- Pump window & daily requirement ----------
int: ND = 1 + (T - 1) div 24;
set of int: Days = 0..ND-1;

int: pump_window_len_hours = pump_window_end_hod - pump_window_start_hod;

% Required hours per day in the horizon
% - Today (dy=0): remaining = target - already done (clipped at 0)
% - Future days: full target (you chose to only penalize today's shortage)
array[Days] of int: pump_required_hours_day =
  array1d(Days,
    [ if dy = 0 then
        max(0, pump_run_hours_min_per_day - pump_hours_done_today)
      else
        pump_run_hours_min_per_day
      endif
    | dy in Days ]
  );

% Hours in the pump window for day 'dy' within the horizon
function set of int: pump_window_hours_for(int: dy) =
  { t | t in H
      where day_index(t) = dy /\
            hour_of_day(t) >= pump_window_start_hod /\
            hour_of_day(t) <  pump_window_end_hod };

% Shortage slack (keeps feasibility); bounded by window length
array[Days] of var 0..pump_window_len_hours: pump_short_hours;

% Meet the (possibly remaining) daily requirement, with slack
constraint forall(dy in Days) (
  let { set of int: Wd = pump_window_hours_for(dy) } in
  sum(t in Wd)(pump_is_on[t]) + pump_short_hours[dy] >= pump_required_hours_day[dy]
);

% Anti-procrastination for today: don't run out of slots
constraint
  let { set of int: W0 = pump_window_hours_for(0) }
  in
  ( if card(W0) > 0 /\ pump_required_hours_day[0] > 0 then
      forall(tau in W0)(
        sum(t in W0 where t <= tau)(pump_is_on[t]) >=
        max(0, pump_required_hours_day[0] - card({ u | u in W0 where u > tau }))
      )
    else true endif
  );

% Allowed window (force OFF outside window)
constraint forall(t in H)(
  if hour_of_day(t) < pump_window_start_hod \/ hour_of_day(t) >= pump_window_end_hod
  then pump_is_on[t] = 0 else true endif
);

% --------- Core physical constraints ----------
% Power balance (1h slots)
constraint forall(t in H)(
  base_load_kw[t]
  + pump_power_kw * pump_is_on[t]
  + batt_charge_kw[t]/eff_charge
  + grid_export_kw[t]
  =
  pv_used_kw[t]
  + batt_discharge_kw[t]*eff_discharge
  + grid_import_kw[t]
);

% You cannot use more PV than is available
constraint forall(t in H)( pv_used_kw[t] <= solar_gen_kw[t] );

% Grid OFF during load shedding: no import/export; pump forced OFF
constraint forall(t in H)(
  if grid_outage_on[t] = 1 then
    grid_import_kw[t] = 0 /\
    grid_export_kw[t] = 0 /\
    pump_is_on[t]     = 0
  else true endif
);

% SOC dynamics (kWh)
constraint soc_kwh[1] = soc0_kwh + batt_charge_kw[1]*eff_charge - batt_discharge_kw[1]/eff_discharge;
constraint forall(t in 2..T)(
  soc_kwh[t] = soc_kwh[t-1] + batt_charge_kw[t]*eff_charge - batt_discharge_kw[t]/eff_discharge
);

% No simultaneous charge & discharge
constraint forall(t in H)(
  batt_charge_kw[t]    <= batt_power_max_kw * (1 - is_discharging[t]) /\
  batt_discharge_kw[t] <= batt_power_max_kw * is_discharging[t]
);

% (Redundant with var bounds; kept for clarity)
constraint forall(t in H)(
  grid_import_kw[t] <= grid_import_max_kw /\
  grid_export_kw[t] <= grid_export_max_kw
);

% Terminal SOC soft band
constraint soc_kwh[T] + terminal_soc_shortfall_kwh >= soc_target_min_kwh;
constraint soc_kwh[T] - terminal_soc_excess_kwh  <= soc_target_max_kwh;

% --- Pre-shedding anchor (simple): arrive at outage starts with >= pre_shed_soc_min_kwh ---
% Applied at the hour BEFORE each outage starts
% If an outage ever starts at t=1, it falls back to checking soc_kwh[1]
array[H] of var 0.0..batt_capacity_kwh: pre_shed_shortfall_kwh;  % kWh below target

function int: prev(int: t) = if t > 1 then t - 1 else 1 endif;  % check end of previous hour if there is one

constraint forall(t in H)(
  if grid_outage_on[t] = 1 /\ (t = 1 \/ grid_outage_on[t-1] = 0) then
    soc_kwh[prev(t)] + pre_shed_shortfall_kwh[t] >= pre_shed_soc_min_kwh
  else
    pre_shed_shortfall_kwh[t] = 0
  endif
);

% Mode change linearization
constraint forall(t in 2..T)(
  mode_change[t] >= is_discharging[t] - is_discharging[t-1] /\
  mode_change[t] >= is_discharging[t-1] - is_discharging[t]
);

% --------- Advice (marginal-cost based) ----------
array[H] of var 0..1: is_expected_export;
constraint forall(t in H)(
  is_expected_export[t] = bool2int(grid_export_kw[t] >= export_surplus_threshold_kw)
);

array[H] of var float: marginal_energy_cost_per_kwh;   % price-like
constraint forall(t in H)(
  marginal_energy_cost_per_kwh[t] =
      price_sell_per_kwh[t] * is_expected_export[t]
    + price_buy_per_kwh[t]  * (1 - is_expected_export[t])
    + pen_advice_discharge_nudge_per_kwh * is_discharging[t]
);

array[H] of var 0..1: advise_discretionary_on;         % 1 = good time to run
constraint forall(t in H)(
  advise_discretionary_on[t] = bool2int(
    (is_expected_export[t] = 1) \/
    (marginal_energy_cost_per_kwh[t] <= cheap_marginal_cost_threshold_per_kwh)
  )
);

% --------- Derived (for debugging/actuation) ----------
array[H] of var float: batt_to_ac_kw =
  [ eff_discharge * batt_discharge_kw[t] - batt_charge_kw[t]/eff_charge | t in H ];

array[H] of var float: net_grid_kw =
  [ grid_import_kw[t] - grid_export_kw[t] | t in H ];

% PV not used (spilled/throttled). For reporting/plots only.
array[H] of var float: pv_spill_kw =
  [ solar_gen_kw[t] - pv_used_kw[t] | t in H ];

% --------- Objective ----------
var float: cost_energy_currency =
  sum(t in H)(
    price_buy_per_kwh[t] * grid_import_kw[t]
  - price_sell_per_kwh[t] * grid_export_kw[t]
  + pen_export_per_kwh * grid_export_kw[t]
  );

var float: cost_batt_wear_currency =
  pen_batt_wear_per_kwh * sum(t in H)( 0.5*(batt_charge_kw[t] + batt_discharge_kw[t]) );

var float: cost_mode_switch_currency =
  pen_mode_switch_per_event * sum(t in 2..T)( mode_change[t] );

var float: cost_terminal_soc_currency =
  pen_terminal_soc_per_kwh * (terminal_soc_shortfall_kwh + terminal_soc_excess_kwh);

var float: cost_pump_shortage_currency =
  pen_pump_shortage_per_hour * pump_short_hours[0];     % penalize *today* only

var float: cost_pre_shed_soc_currency =
  pen_pre_shed_soc_per_kwh * sum(t in H)( pre_shed_shortfall_kwh[t] );

var float: cost_total_currency =
  cost_energy_currency + cost_batt_wear_currency + cost_mode_switch_currency
  + cost_terminal_soc_currency + cost_pump_shortage_currency
  + cost_pre_shed_soc_currency;

solve minimize cost_total_currency;

% --------- Output ----------
output [
  "summary: cost=", show(cost_total_currency),
  " | end_soc_kwh=", show(soc_kwh[T]),
  " | pump_short_today_h=", show(pump_short_hours[0]), "\n",

  "cost_energy = ", show(cost_energy_currency), "\n",
  "cost_batt_wear = ", show(cost_batt_wear_currency), "\n",
  "cost_mode_switch = ", show(cost_mode_switch_currency), "\n",
  "cost_terminal_soc = ", show(cost_terminal_soc_currency), "\n",
  "cost_pump_shortage = ", show(cost_pump_shortage_currency), "\n",
  "cost_pre_shed_soc_currency = ", show(cost_pre_shed_soc_currency), "\n",
  "All values at end of the hour:\n",
  "grid_import_kw = ", show(grid_import_kw), "\n",
  "grid_export_kw = ", show(grid_export_kw), "\n",
  "batt_charge_kw = ", show(batt_charge_kw), "\n",
  "batt_discharge_kw = ", show(batt_discharge_kw), "\n",
  "batt_to_ac_kw = ", show(batt_to_ac_kw), "\n",
  "soc_kwh = ", show(soc_kwh), "\n",  
  "is_discharging = ", show(is_discharging), "\n",
  "pv_used_kw = ", show(pv_used_kw), "\n",
  "pv_spill_kw = ", show(pv_spill_kw), "\n",
  "pump_is_on = ", show(pump_is_on), "\n",
  "mode_change = ", show([ mode_change[t] | t in 2..T ]), "\n",
  "advise_discretionary_on = ", show(advise_discretionary_on), "\n",
  "marginal_energy_cost_per_kwh = ", show(marginal_energy_cost_per_kwh), "\n",
  "terminal_soc@t=36 = {below_target_min_kwh=", show(terminal_soc_shortfall_kwh),
  ", above_target_max_kwh=", show(terminal_soc_excess_kwh), "}\n"
];
