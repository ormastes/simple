# Shard concurrency was derived from CPU count alone — worker group OOM-reaped mid-HIR

- Date: 2026-08-23
- Status: FIXED (clamp landed); the underlying per-worker footprint is tracked
  separately in `doc/09_report/rust-perf-limits.md`.
- Related: `doc/09_report/build_parallelism_memory_audit_2026-08-23.md` §2, §4

## Symptom

`native-build` stage1 runs were killed, not merely slow:

```
native-build worker wrapper exited abnormally (signal or wait failure, code -1)
… process group terminated
```

run17 terminated `rc=255` after 12,643 s across 3 attempts; the death point
differed every time (HIR 13/688, 288/688, 509/688), so it is not a deterministic
compiler defect. `MemAvailable` was ~16 GB of 125 GB. run18 and two probe runs
carry the same signature. At least four runs were lost this way, and every
stage1 measurement taken that day was at risk from it.

## Root cause

The shard thread count was a pure function of CPU count and never of memory.

- `src/app/cli/native_build_main.spl:native_build_shard_threads` read
  `--threads/--jobs/-j` and returned it unchanged.
- The real chooser, `scripts/bootstrap/bootstrap-from-scratch.sh:897-945`, sets
  `jobs=$((host_cpus / 2))` — **16** on this 32-core host.
- A measured worker holds 2.40-2.74 GB RSS (VmPeak 3.37 GB), 99.4% anonymous,
  `Pss ≈ Rss` so siblings share only ~14 MB. 16 × ~2.5-3.3 GB ⇒ **~40 GB
  requested by a single run**, on a box also carrying ~10 other lanes.
- No backoff of any kind existed. The only reader of `/proc/meminfo` in the
  build path, `scripts/check/check-heavy-work-preflight.shs:100-141`, is a
  one-shot admission gate: it *refuses to start*, it never lowers N.
  `SIMPLE_BOOTSTRAP_LOW_MEMORY=1` selects a static code path, not a response to
  pressure.

## Fix

New module `src/app/cli/shard_mem_clamp.spl`, called from
`native_build_shard_threads` for both shard phases:

```
cap = max(1, floor(MemAvailable_kB * 0.6 / worker_budget_kB))
threads = min(requested, cap)
```

Per-phase budgets, because the two phases are not alike: parse shards run the
slim parse-lane entry (1.65 GB, the same constant
`scripts/check/check-parse-shard-rss-budget.shs` pins), while HIR shards still
spawn the full worker closure (3.0 GB, measured). HIR is therefore clamped
harder — which matters, since every observed kill was in HIR.

Measured effect on this box at `MemAvailable = 21,958,928 kB`, request 16:

| phase | before | after | asked-for RSS before → after |
|---|---|---|---|
| parse shards | 16 | **7** | 26 GB → 11.6 GB |
| HIR shards | 16 | **4** | 48 GB → 12 GB |

## Why this is safe

Shard phases are a **cache warm-up**: the compiled output is byte-identical at
any N, so reducing N is semantics-preserving by construction. The clamp only
ever *lowers* the count, never raises it; unknown memory (`MemAvailable`
missing, non-Linux) returns the request untouched, so absence of evidence never
increases concurrency; it never returns 0 workers. It reads one file once at
spawn time and is deliberately **not** a mid-run feedback loop — killing or
suspending live shards would re-open the orphaned-claim class fixed by
`6cedd51faec`. `SIMPLE_SHARD_MEM_CLAMP=0` disables it;
`SIMPLE_PARSE_SHARD_WORKER_KB` / `SIMPLE_HIR_SHARD_WORKER_KB` override the
budgets.

## Test

`test/01_unit/app/cli/shard_mem_clamp_spec.spl` — 7 examples, 455 ms. Pins the
mechanism (cap arithmetic, per-phase asymmetry, the never-raise and
never-zero invariants, the unknown-memory skip), not wall-clock. Neuter check:
replacing the cap computation with `cap = requested` turns 3 of the 7 red;
restoring it turns them green. Ratcheted by
`scripts/check/check-perf-regression-tests.shs`.

## Not fixed here

The clamp bounds the damage; it does not reduce the 2.5-3.3 GB per worker.
Everything about that footprint that cannot be fixed without changing the
architecture is recorded in `doc/09_report/rust-perf-limits.md`.
