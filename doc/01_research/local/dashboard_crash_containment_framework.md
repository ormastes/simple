<!-- codex-research -->
# Dashboard Crash Containment Framework — Local Research

Date: 2026-04-03
Scope: dashboard / LLM dashboard crash isolation, default app budgets, process fault domains

## Current Local State

- [`src/app/dashboard/main.spl`](/home/ormastes/dev/pub/simple/src/app/dashboard/main.spl) now routes heavy dashboard commands through [`src/app/dashboard/framework_policy.spl`](/home/ormastes/dev/pub/simple/src/app/dashboard/framework_policy.spl).
- [`src/app/dashboard/framework_policy.spl`](/home/ormastes/dev/pub/simple/src/app/dashboard/framework_policy.spl) isolates `collect`, `export`, `query`, `compare`, `serve`, `gui`, and `agents --gui` into child workers.
- [`src/os/crash_policy.spl`](/home/ormastes/dev/pub/simple/src/os/crash_policy.spl) defines default fault domains and runtime budgets:
  - Interactive / dashboard / LLM defaults: `8192 MB`
  - Heavy compiler: `16384 MB`
  - Heavy test runner / indexer: `12288 MB`
  - Normal workloads: half of available threads
  - Heavy workloads: all threads or capped high-water marks
- [`src/os/desktop/app_manifest.spl`](/home/ormastes/dev/pub/simple/src/os/desktop/app_manifest.spl) already imports crash-policy defaults for launcher metadata.
- Rust logging startup was hardened in:
  - [`src/compiler_rust/log/src/lib.rs`](/home/ormastes/dev/pub/simple/src/compiler_rust/log/src/lib.rs)
  - [`src/compiler_rust/driver/src/log.rs`](/home/ormastes/dev/pub/simple/src/compiler_rust/driver/src/log.rs)
  - [`src/compiler_rust/driver/src/cli/init.rs`](/home/ormastes/dev/pub/simple/src/compiler_rust/driver/src/cli/init.rs)
  These changes avoid panicking when the preferred log directory is not writable.

## Important Gaps Found

1. Policy existed before enforcement was complete.
   Heavy dashboard commands were isolated, but the child shell did not export the memory budget back into the child runtime, so the Rust watchdog path could run without the same configured ceiling.

2. Long-running workers rely on process containment, not session-local recovery.
   `run_supervised_worker()` restarts crashed workers, but it does not preserve structured crash metadata beyond exit code classification.

3. Thread budgeting is policy-first, not runtime-universal.
   The framework exports `RAYON_NUM_THREADS` and `TOKIO_WORKER_THREADS`, but there is no general-purpose Simple runtime consumer of `SIMPLE_THREAD_BUDGET` yet.

4. Container workflow documentation is stale.
   Multiple docs and compose files still point to `docker/Dockerfile.*`, but the actual maintained Dockerfiles live under [`tools/docker`](/home/ormastes/dev/pub/simple/tools/docker).

5. Existing dashboard system spec is stale-path oriented.
   [`test/system/infrastructure/dashboard_system_spec.spl`](/home/ormastes/dev/pub/simple/test/system/infrastructure/dashboard_system_spec.spl) still targets `doc/dashboard/...` and direct `.spl` execution instead of the current `simple dashboard` CLI path and current `doc/10_metrics/dashboard/...` layout.

## Existing Runtime Enforcement Mechanisms

- Shell-level resource caps:
  - [`src/lib/nogc_sync_mut/io/process_limit_enforcer.spl`](/home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/io/process_limit_enforcer.spl)
  - [`src/lib/nogc_sync_mut/io/process_ops.spl`](/home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/io/process_ops.spl)
  These apply `ulimit -v`, `-t`, `-n`, and `-u` for one-shot workers and can classify timeout/memory/fd/proc failures.

- Rust watchdog enforcement:
  - [`src/compiler_rust/compiler/src/watchdog.rs`](/home/ormastes/dev/pub/simple/src/compiler_rust/compiler/src/watchdog.rs)
  This already reads `SIMPLE_MEMORY_LIMIT_MB` and `SIMPLE_TIMEOUT_SECONDS`, monitors RSS, and trips a timeout fault when limits are exceeded.

## Container Findings

- Docker daemon is available on this machine.
- `docker compose` plugin is not installed.
- `docker-compose` is also not installed.
- The practical container path in this repo is direct `docker build` / `docker run` using [`tools/docker/Dockerfile.test-isolation`](/home/ormastes/dev/pub/simple/tools/docker/Dockerfile.test-isolation).

## Working Assumption Taken From User Request

The user request is treated as explicit selection of these defaults:

- Default hosted app memory ceiling: less than `10 GB`
- Default hosted app threads: half of available parallelism
- Heavy exceptions only for compiler, test runner, and comparable batch workers
- Kernel/baremetal domains must fail differently from hosted user apps
- Dashboard and LLM dashboard crashes must not take down the user session or platform
