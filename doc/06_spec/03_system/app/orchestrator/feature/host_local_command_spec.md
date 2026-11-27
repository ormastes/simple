# Finite local host command boundary

Status: **NOT_RUN**. Authored from the executable spec; no generated execution
report or production qualification is claimed.

Source: `test/03_system/app/orchestrator/feature/host_local_command_spec.spl`.

| Scenario | Observable prevention |
|---|---|
| Unknown command/incomplete arguments | Exit 1 before opening an owner |
| Invalid signed execute packet | No journal or provider directory created |
| Interrupted policy publication | Exact claim retained, existing object unchanged, runtime-ready never published |
| Canonical binding round trip | Re-encoding exact; altered kind/trailing bytes rejected |
| Real signed claim with changed retained Container policy | Policy digest mismatch refuses before native provider or journal creation; claim retained |
| Interrupted claim/edited configuration | Root remains claimed; no capacity journal opens |

Native-positive execution, command races and post-effect crash qualification are
listed in `doc/03_plan/sys_test/host_local_execution.md` and remain unexecuted.
