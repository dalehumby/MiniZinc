% ===============================
% Production-ish battery dispatcher + pool pump
% Rolling horizon, MPC-friendly
% ===============================

% --------- Sets & horizon ---------
int: T;                        % e.g., 36 or 48
set of int: H = 1..T;

% Helpers to map time index to day/hour-of-day
int: start_hod;                             % hour-of-day at horizon t=1 (0..23)
function int: hod_of(int: t) = (start_hod + (t - 1)) mod 24;
function int: day_of(int: t) = (start_hod + (t - 1)) div 24;

% --------- Inputs (data) ----------
array[H] of float: S;          % solar generation (kW)
array[H] of float: L;          % house base load (kW)
array[H] of float: pb;         % buy price (currency/kWh)
array[H] of float: ps;         % sell price (currency/kWh)

float: C;                      % battery capacity (kWh)
float: Pmax;                   % max charge/discharge power (kW)
float: eta_c;                  % charge efficiency (0..1)
float: eta_d;                  % discharge efficiency (0..1)
float: x0;                     % initial SOC (kWh)
float: xmin;                   % min SOC (kWh)
float: xmax;                   % max SOC (kWh)

% Interconnect limits
float: GridImportMax;
float: GridExportMax;

% Costs / penalties
float: alpha;                  % wear proxy (currency/kWh)
float: lambda_terminal;        % terminal SOC band penalty (currency/kWh)
float: lambda_switch;          % charge/discharge switch penalty (currency per switch)
float: beta_export;            % export penalty (currency/kWh), 0 if none

% Soft terminal SOC band (end-of-horizon)
float: x_target_min;
float: x_target_max;

% Parameters controlling advice heuristics
float: cheap_threshold;
float: eps_export;
float: discharge_pen;

% ---------- Pool pump parameters ----------
float: pump_kw;                % pump power when ON (kW)
int:   pump_min_hours_per_day; % e.g., 6
int:   pump_start_hour;        % e.g., 8   (08:00 inclusive)
int:   pump_end_hour;          % e.g., 20  (20:00 exclusive)
int:   pump_hours_done_today;  % e.g., 3
float: lambda_pump_shortage; % e.g., 10.

% --------- Decision variables ----------
array[H] of var 0.0..GridImportMax: g_import;
array[H] of var 0.0..GridExportMax: g_export;
array[H] of var 0.0..Pmax:          c;
array[H] of var 0.0..Pmax:          d;
array[H] of var xmin..xmax:         x;

% y=1 => discharging; y=0 => charging
array[H] of var 0..1: y;

% Pump on/off (adds pump_kw to load when 1)
array[H] of var 0..1: pump_on;

% Slack for terminal SOC band (upper bound to limit model)
var 0.0..1.0e6: s_below;
var 0.0..1.0e6: s_above;

% Mode switching absolute value linearization
array[2..T] of var 0.0..1.0: z;

% --------- Constraints ----------

% Allowed window for the pump: force OFF outside [start, end)
constraint forall(t in H)(
  if hod_of(t) < pump_start_hour \/ hod_of(t) >= pump_end_hour
  then pump_on[t] = 0 else true endif
);

% --- Per-day minimum pump hours with current-day remainder & anti-procrastination ---

% Horizon days (day 0 is "today" at the current solve time)
int: ND = 1 + (T - 1) div 24;
set of int: Days = 0..ND-1;

% Required hours per day in the horizon:
% - Today (dy=0): remaining = target - already done (clipped at 0)
% - Future days: full target
% Days = 0..ND-1
array[Days] of int: pump_req_day =
  array1d(Days,
    [ if dy = 0 then
        max(0, pump_min_hours_per_day - pump_hours_done_today)  % today
      else
        pump_min_hours_per_day                                  % future days
      endif
    | dy in Days
    ]
  );


% Helper: window set for any day 'dy'
function set of int: pump_window_for(int: dy) =
  { t | t in H
      where day_of(t) = dy /\
            hod_of(t) >= pump_start_hour /\
            hod_of(t) <  pump_end_hour };

% --- Shortage slack (keeps model feasible but penalizes any unmet hours) ---
% At most 24 shortfall per day; adjust if you ever widen the window.
array[Days] of var 0..24: pump_short;

constraint forall(dy in Days) (
  let { set of int: Wd = pump_window_for(dy) } in
  sum(t in Wd)(pump_on[t]) + pump_short[dy] >= pump_req_day[dy]
);

% --- Anti-procrastination for *today* (dy=0) ---
% Ensure we don't delay so long that it's impossible to meet today's remaining hours.
% For each prefix of today's remaining window, we must have run enough hours already
% to still be able to meet the target with the slots left after that prefix.
constraint
  let { set of int: W0 = pump_window_for(0) }
  in
  ( if card(W0) > 0 /\ pump_req_day[0] > 0 then
      forall(tau in W0)(
        sum(t in W0 where t <= tau)(pump_on[t]) >=
        max(0, pump_req_day[0] - card({ u | u in W0 where u > tau }))
      )
    else true endif
  );


% Power balance (pump adds to load when ON)
constraint forall(t in H)(
  L[t] + pump_kw * pump_on[t] + c[t]/eta_c + g_export[t]
  = S[t] + d[t]*eta_d + g_import[t]
);

% SOC dynamics
constraint x[1] = x0 + c[1]*eta_c - d[1]/eta_d;
constraint forall(t in 2..T) (
  x[t] = x[t-1] + c[t]*eta_c - d[t]/eta_d
);

% No simultaneous charge & discharge
constraint forall(t in H) (
  c[t] <= Pmax * (1 - y[t]) /\
  d[t] <= Pmax * y[t]
);

% Interconnect limits (redundant with var bounds, kept for clarity)
constraint forall(t in H) (
  g_import[t] <= GridImportMax /\ g_export[t] <= GridExportMax
);

% Soft terminal SOC band
constraint x[T] + s_below >= x_target_min;
constraint x[T] - s_above <= x_target_max;

% Mode switching penalty helper
constraint forall(t in 2..T) (
  z[t] >= y[t] - y[t-1] /\
  z[t] >= y[t-1] - y[t]
);

% --- Advice (marginal-cost based) ---

% Flag when we expect surplus (export) this hour
array[H] of var 0..1: export_flag;
constraint forall(t in H)(
  export_flag[t] = bool2int(g_export[t] >= eps_export)
);

% Marginal cost to run +1 kWh in hour t:
%   - if surplus (export): you give up ps[t]
%   - else: you must buy at pb[t]
%   - small nudge to discourage hours when model is in discharge mode (y=1)
array[H] of var float: marginal_cost;
constraint forall(t in H)(
  marginal_cost[t] = ps[t] * export_flag[t]
                   + pb[t] * (1 - export_flag[t])
                   + discharge_pen * y[t]
);

% Advice flag: good if we expect surplus OR marginal cost is “cheap”
array[H] of var 0..1: good_time_discretionary;
constraint forall(t in H)(
  good_time_discretionary[t] = bool2int(
    (export_flag[t] = 1) \/
    (marginal_cost[t] <= cheap_threshold)
  )
);

% Score: higher is better (cheaper). This is just for reporting/plotting.
array[H] of var float: advice_score =
  [ -marginal_cost[t] | t in H ];


% --------- Objective ----------

% --- Cost components ---
var float: cost_energy =
  sum(t in H)( pb[t]*g_import[t] - ps[t]*g_export[t] + beta_export * g_export[t] );

var float: cost_wear   = alpha * sum(t in H)( 0.5*(c[t] + d[t]) );
var float: cost_switch = lambda_switch * sum(t in 2..T)( z[t] );
var float: cost_term   = lambda_terminal * (s_below + s_above);

% If you included pump shortage slack:
%var float: cost_pump   = lambda_pump_shortage * sum(dy in Days)( pump_short[dy] );
var float: cost_pump = lambda_pump_shortage * pump_short[0];

var float: cost_total  = cost_energy + cost_wear + cost_switch + cost_term + cost_pump;

solve minimize cost_total;


% --------- Output ----------
output [
  "cost = ", show(cost_total), "\n",
  "cost_energy = ", show(cost_energy), "\n",
  "cost_wear = ", show(cost_wear), "\n",
  "cost_switch = ", show(cost_switch), "\n",
  "cost_terminal = ", show(cost_term), "\n",
  "cost_pump_shortage = ", show(cost_pump), "\n",
  "g_import = ", show(g_import), "\n",
  "g_export = ", show(g_export), "\n",
  "c = ", show(c), "\n",
  "d = ", show(d), "\n",
  "x = ", show(x), "\n",
  "y = ", show(y), "\n",
  "pump_on = ", show(pump_on), "\n",
  "switches = ", show([ z[t] | t in 2..T ]), "\n",
  "good_time_discretionary = ", show(good_time_discretionary), "\n",
  "advice_score = ", show(advice_score), "\n",
  "terminal_slack = {below=", show(s_below), ", above=", show(s_above), "}\n"
];
