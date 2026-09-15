---- MODULE Smoke_BaseSpec ----
\* Throwaway parse/reachability smoke test -- NOT a real correctness claim about this
\* domain. Confirms TLC can parse BaseSpec_AlarmManager.tla's full composition (both
\* Component_Pump instances, Component_AlarmManager, Infrastructure_Channel) and compute
\* Init plus a bounded number of Next steps with no error.
EXTENDS BaseSpec_AlarmManager, TLC

SmokeBound == TLCGet("level") <= 8

====
