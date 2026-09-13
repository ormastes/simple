# Bootstrap job selection

`scripts/bootstrap/bootstrap-jobs.shs` provides one CPU-selection function for
the bootstrap driver and its self-hosted native builds:

```sh
. scripts/bootstrap/bootstrap-jobs.shs
bootstrap_select_jobs "${jobs:-}" config/bootstrap.sdn
```

The function sets `host_cpus`, `jobs`, `selfhost_jobs`, and `job_source` in the
caller. Selection priority is explicit `--jobs`, existing
`SIMPLE_NATIVE_BUILD_THREADS`, a `jobs:` or `native_build_threads:` entry in the
selected bootstrap config, then all detected online CPUs. Explicit `auto` and
`full` mean all detected CPUs, `half` means half, and `min`/`minimal`/`minimum`
mean one. A valid explicit numeric value is honored even when it exceeds the
detected CPU count; the operator owns that override. Numeric values are bounded
to 65535 so shell integer comparisons and downstream worker counts remain
well-defined.

An invalid explicit CLI value fails because the operator asked for that exact
setting. Invalid environment or config values emit a diagnostic and safely use
all detected CPUs. CPU discovery tries affinity-aware `nproc` before `getconf`,
`sysctl`, and the Windows processor-count environment. If every probe is
invalid or zero, the helper emits a diagnostic and uses one worker.
`job_source` records `cli`, `env`, `config`,
`default`, or the corresponding fallback so receipts cannot hide the decision.

The bootstrap driver now applies the selected value equally to `jobs` and
`selfhost_jobs`; the legacy implicit half-CPU default and incremental-profile
cap of two are gone. It writes `build/bootstrap/selected-build-jobs.env` (or the
selected output root equivalent) with `host_cpus`, `jobs`, `selfhost_jobs`, and
`source`. All four hermetic Rust seed/runtime/backfill Cargo envelopes receive
the same value through `CARGO_BUILD_JOBS`. Stage 2 receives explicit
`--threads`; Stage 3 receives both explicit `--threads` and
`SIMPLE_NATIVE_BUILD_THREADS`. This removes an inherited environment override
from the recorded build identity while preserving each phase command contract.

`SIMPLE_NATIVE_LOW_MEMORY=1` remains an explicit operator opt-in. Its default
is `0`, so it no longer silently reduces the selected parallel worker policy.
Worker counts do not authorize multiple writers to one native cache; cache
ownership rules remain unchanged. Phase feature receipts independently repeat
the selected job count and detected CPU count.

Focused contract:

```sh
sh test/01_unit/scripts/bootstrap_jobs_policy_test.shs
```
