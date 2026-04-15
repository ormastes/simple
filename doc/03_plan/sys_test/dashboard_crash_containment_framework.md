<!-- codex-design -->
# System Test Plan — Dashboard Crash Containment Framework

Date: 2026-04-03

## Target Scenarios

1. `simple dashboard collect` runs in an isolated worker and returns normal output.
2. `simple dashboard serve` restarts on abnormal worker exit up to the configured limit.
3. Worker shell command exports the selected memory and timeout budgets.
4. Default dashboard / LLM worker profiles stay below `10 GB`.
5. Default interactive profiles use half of available threads.
6. Heavy compiler/test workloads retain larger budgets.
7. Bare-metal profile does not inherit hosted resource/time limits.
8. Bare-metal simplified policy is documented separately and stays out of dashboard-style restart loops.

## Validation Strategy

- Unit/spec validation for policy mapping and worker command generation.
- Command-level container validation for `simple dashboard` paths.
- Docker is the required execution boundary for this work; do not validate the dashboard fix on the host.
- Follow-up system-spec refresh to replace stale direct-`.spl` dashboard tests with current CLI-path tests.
- Reference the generic framework plan for bare-metal panic/watchdog verification rather than reusing dashboard restart cases.
