# Shard concurrency was derived from CPU count alone — worker group OOM-reaped mid-HIR

- Date: 2026-08-23
- Status: **RE-LANDED 2026-08-23** after a revert. First landing
  (`ff095d31591`) aborted every `native-build` with `rc=134, fatal runtime
  error: stack overflow` before step 0/6, on a 3-line hello world with
  `--threads 2`. Reverted in `765f9d2aad4`; root cause was **not** the clamp
  logic but `file_read`, which infinitely recurses in the run20-class seed on
  ANY file — `seed_file_read_infinite_recursion_stack_overflow_2026-08-23.md`.
  Re-landed reading MemAvailable via `process_run_timeout("awk", ...)`.
- Underlying finding (unchanged and still correct); the underlying per-worker footprint is tracked
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

Confirmed live on the real path after the re-land:
`[shard] threads=11 (requested 16, capped by MemAvailable=32227176 kB / worker budget 1650000 kB)`, build then proceeding past `step 1/6`.

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

## What the first landing got wrong, and the fix to the process

The shipped spec was 7 mechanism-pinned examples and it **passed while the real
path crashed**: it exercised the clamp *function* and never the *call path*.
That is the same class as "code that compiled and executed zero times". Nothing
in the tree ran `native-build` end to end, so nothing could have caught it.

New gate `scripts/check/check-native-build-not-crashing.shs` runs the real
driver on a hello world at `--threads 2` and `--threads 16` and asserts it does
not die by signal. Verified in both directions on the run20 seed:

| tree | gate verdict |
|---|---|
| the broken `ff095d31591` clamp restored | `FAIL — 2 invocation(s) executed, 2 crashed` (`rc=134`, `progressed=no`) |
| the re-landed clamp | `PASS — 2 invocation(s) executed, 0 crashes` |

Bisect that isolated it (each step a real `native-build`):

| variant | result |
|---|---|
| clamp as landed | rc=134 |
| `shard_threads_mem_cap` body → `requested` | rc=124, no crash |
| full body, `/proc` read replaced by a constant | rc=124, no crash |
| **`file_read` called, result discarded, never parsed** | **rc=134** |

## Test

`test/01_unit/app/cli/shard_mem_clamp_spec.spl` — 7 examples, 455 ms. **Necessary but provably not sufficient** (see above); the end-to-end bar is `check-native-build-not-crashing.shs`. Pins the
mechanism (cap arithmetic, per-phase asymmetry, the never-raise and
never-zero invariants, the unknown-memory skip), not wall-clock. Neuter check:
replacing the cap computation with `cap = requested` turns 3 of the 7 red;
restoring it turns them green. Ratcheted by
`scripts/check/check-perf-regression-tests.shs`.

## Not fixed here

The clamp bounds the damage; it does not reduce the 2.5-3.3 GB per worker.
Everything about that footprint that cannot be fixed without changing the
architecture is recorded in `doc/09_report/rust-perf-limits.md`.
