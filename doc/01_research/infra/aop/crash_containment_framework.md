<!-- codex-research -->
# Local Research: Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## Scope

Research the existing repo paths that already influence crash isolation, panic handling, restart behavior, and runtime budgeting for dashboard and platform workloads.

## Relevant Existing Code

- `src/os/crash_policy.spl`
  - Introduces repo-level policy types:
    - `AppClass`
    - `AppFaultDomain`
    - `SupervisorPolicy`
    - `AppWorkloadProfile`
    - `RuntimeBudget`
  - Encodes the requested defaults:
    - interactive/dashboard/LLM memory cap: `8192 MB`
    - heavy workloads may exceed that default
    - thread default: half of `rt_thread_available_parallelism()`
    - baremetal domain: single-threaded, no host-style soft limits

- `src/app/dashboard/framework_policy.spl`
  - Wraps dashboard work in child processes instead of letting the parent dashboard/session absorb crashes directly.
  - Exports environment throttles:
    - `SIMPLE_THREAD_BUDGET`
    - `RAYON_NUM_THREADS`
    - `TOKIO_WORKER_THREADS`
  - Applies `ulimit`-based resource controls before worker launch.
  - Maintains restart history for supervised commands.

- `src/app/dashboard/main.spl`
  - Routes heavy or long-running dashboard commands through framework workers:
    - `collect`
    - `export`
    - `query`
    - `compare`
    - `serve`
    - `gui`
    - `agents --gui|--web`
  - This is the current containment boundary for the dashboard path.

- `src/os/desktop/app_manifest.spl`
  - Each manifest now carries:
    - `app_class`
    - `fault_domain`
    - `supervisor_policy`
  - This is the right place to make crash containment default across hosted apps, not dashboard-only.

- `src/compiler_rust/driver/src/cli/init.rs`
  - Rust logging init now resolves a writable log directory instead of assuming `.simple/logs` is always usable.
  - Panic hook already emits structured crash diagnostics and writes crash files.

- `doc/09_report/session/examples_safe_failure_2026-03-31.md`
  - Prior session already identified the core architectural issue:
    command boundaries do not consistently normalize failures into classified outcomes.

## Important Current Gaps

### 1. Supervised long-running workers were not using the same limit-aware execution path

Before this session's patch, `run_supervised_worker()` used:

- `process_spawn_async()`
- `process_wait()`

That path restarted crashed workers, but it did not preserve:

- limit classification (`memory`, `cpu`, `timeout`, `fds`, `procs`)
- child output capture
- consistent failure normalization with one-shot workers

### 2. `timeout_ms = 0` did not mean "no timeout" in `process_run_with_limits()`

`process_run_with_limits()` treated non-positive timeout as a 120 second default.

Impact:

- long-running services could not safely reuse the limit-aware path
- framework code had to bypass the safer executor
- the repo semantics for "unlimited wall timeout" were inconsistent

### 3. Policy exists, but platform-wide enforcement is only partially wired

The repo now has policy declarations for:

- fault domain
- restart strategy
- workload class
- resource caps

But the broad platform still lacks one uniform launcher/supervisor boundary for every hosted app and service.

## Selected Direction From Current User Request

The user already selected these defaults in the request:

- crash containment should be systematic, not dashboard-specific
- default max memory should be less than `10 GB`
- heavy workers such as compiler/test runner may exceed the default
- default thread budget should be half of system parallelism
- baremetal must be treated differently and may escalate to halt/reboot rather than soft restart

## Implementation Consequence

The repo should standardize on:

1. Process fault domains for user apps and dashboard-style sessions.
2. Supervised task domains for services.
3. Kernel-resident components escalating harder than hosted apps.
4. Baremetal domains using trap/panic handlers that stop or reboot the domain, not "recover in place".
