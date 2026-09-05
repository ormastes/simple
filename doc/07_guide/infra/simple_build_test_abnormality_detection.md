# Build/Test Abnormality Detection

Simple distinguishes three independent mechanisms:

- a hard execution scope protects the machine and process tree;
- a declared budget produces a deterministic project-policy result;
- an approved historical baseline detects introduced regressions.

Never describe exit 137 as proof of timeout/OOM or 139 as proof of memory exhaustion. Read the structured termination cause and evidence quality. `ExactTree` means the provider observed the whole execution scope; `ExactDirectChild`, `SampledTree`, `ProcessOnly`, and `Unavailable` are intentionally weaker.

Normal comparisons require the same scenario, semantic configuration, workload/aspect plan, and machine class. `full_cold`, warm-cache, incremental, check, debug, opt, and bootstrap stages are separate cohorts. A new cohort is provisional: hard limits and declared budgets still apply, but historical failure does not until an approved baseline exists.

Approved baselines are immutable observations. Recording or comparing a candidate never promotes it. Promotion is an explicit reviewed action, and a previous approved generation becomes superseded rather than disappearing.

The default robust policy requires an absolute floor, a relative floor, and a MAD noise floor simultaneously. Warnings start at 10%/3 MAD; failures start at 15%/4 MAD and require confirmation. Outliers and tail metrics remain stored.

Provider diagnostics should explain the first unavailable rung. On Linux prefer delegated cgroup v2 tree evidence, then direct-child `wait4`, sampled tree, and finally process-only/RLIMIT watchdog evidence. Windows retains execution through the existing Job Object owner but its new observed budget receipt is still blocked; macOS retains process-group/RLIMIT execution while its pidfd-free observed receipt is blocked. Unsupported native rows remain blocked, not simulated PASS.

`simple perf` operates on the same persisted test evidence:

- `record <subject> <cohort> <duration-ms>` appends a positive observation;
- `compare <subject> <cohort> <candidate-ms> [--confirmed]` prints thresholds and returns 1 for a confirmed failure, 2 for incomplete/invalid evidence, and 0 for pass/warning;
- `explain <subject>` prints the approved generation, cohort, samples, and provisional median;
- `baseline promote <subject> <cohort>` is the only baseline mutation command.

Builds write stable subjects separately from volatile runs and external span/artifact digests. Core interpreter, SMF, native, safe, fork, baremetal-host, and QEMU-host test paths attach the same class/cohort/budget fields. Fork evidence is direct-child `wait4`; it is never labeled tree evidence.

The executable scenario is `test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl`; the operator manual is under `doc/06_spec/03_system/app/perf/feature/`.

On Linux without direct controller delegation, the explicit systemd provider can retain `MemoryPeak`, `oom-kill`, and live `pids.events` evidence. It also distinguishes a supervisor-requested SIGTERM from an unexplained 143 exit. On Windows/macOS, the bounded compatibility path remains functional while the observed receipt reports `Unavailable`; follow the linked platform TODOs before claiming native parity.
