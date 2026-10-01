# SOSIX process and environment route manifest v1

Status: partial RU-001 source census at `7b3cfd5a280`. This documents an
admission gap; it does not qualify hosted or SimpleOS process execution.

| Route | Current source owner | Admission state |
|---|---|---|
| Shared launch value | `src/lib/common/contracts/execution/process_launch_spec_v1.spl` | Bounded validation and copy exist for executable, argv, environment, cwd, stdio, namespace, limits, affinity, profile, capabilities, and grants. No process effect occurs here. |
| SimpleOS service adapter | `src/os/sosix/process_launch_provider_v1.spl` | Checks a capability reference and launch shape, then calls an injected service owner. Live grants and child execution are still delegated; this adapter alone proves no guest compiler launch. |
| Hosted two-argument spawn | `src/lib/nogc_sync_mut/io/process_ops.spl` and `src/lib/nogc_async_mut/sosix/host_facade.spl` | Command plus argv reaches the hosted runtime. The facade does not accept the shared launch value or its environment/cwd/limits. Interpreter stdin is null; C fork/exec inherits stdin, so even stdio policy differs. |
| App explicit-environment wrapper | `src/app/io/process_env_ops.spl` | Declares a three-source-argument `rt_process_spawn_async`. The interpreter ignores the map and the native C symbol has no map parameter; see `doc/08_tracking/bug/host_process_spawn_env_abi_gap_2026-09-26.md`. Exclude this route from SOSIX admission. |
| Ordinary compiler under SimpleOS | REQ-010 in `doc/02_requirements/feature/simple_platform_unification.md` | Requires filesystem, VM, process, environment, time, random, task/wait, and library/provider services plus version, guest compile, and guest-produced artifact execution. This route is not demonstrated. |

Next work is a single hosted process-service owner with a versioned full-spec
backend contract and explicit unsupported-field refusal, followed by a
source-matched interpreter/native/guest behavior matrix. The current app
wrapper cannot be treated as a working environment bridge.
