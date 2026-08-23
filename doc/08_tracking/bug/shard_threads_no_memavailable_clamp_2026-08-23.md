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

## Reproduce guard (added 2026-08-23)

`scripts/check/check-native-build-hello-world-runs.shs` is the missing test the
revert commit promised. It runs the real `native-build` on a real 3-line hello
world with `--threads 2` and asserts the two properties the incident violated:

1. the process does not die by signal (rc >= 128; 134 = abort/stack overflow), and
2. a `[build] ... step 1/6` line actually appears.

`rc=0` alone is deliberately NOT accepted, and `--version` answering cleanly is
deliberately NOT accepted — the incident printed a healthy banner and then
aborted, which is precisely why it looked fine. Once the step line appears the
guard stops the child *it* started; a full hello-world `native-build` measured
>5 min under the seed on this host, and a guard too slow to run protects nothing.

Discrimination, measured 2026-08-23 (fixtures driven through the shipping probe):

```
--- PRE-FIX SHAPE (aborts 134 before any [build] line):
FAIL — native-build crashed on a 3-line hello world (rc=134, signal 6) before reaching '[build] ... step 1/6'   rc=1
--- POST-FIX SHAPE (reaches step 1/6):
PASS — 1 invocation(s) executed, '[build] ... step 1/6' reached without a crash  rc=0
```

Nine selftest fixtures, fatal and run before every scan: healthy, the incident
shape (banner then SIGABRT), SEGV, plain non-zero exit, silent `exit 0` with no
pipeline line, hang, delayed step line, plus two provenance fixtures.

### Honest limitation: the seed cannot reproduce this, so the seed is REFUSED

The pre-fix tree was checked out (`ff095d31591`, clamp present) and driven with
the same guard against the Rust seed. It **passed** — reaching
`[build] ... step 1/6` with no crash — because the seed serves `native-build`
from its own compiled-in Rust implementation and never executes
`src/app/cli/native_build_main.spl`, hence never calls the clamp. Running
`src/app/cli/native_build_main.spl` under `simple run` instead was measured at
rc=124 with **0** `[build]` lines in 120 s: the interpreted path is far too slow
to serve as a gate.

Rather than ship a guard that green-lights a binary it cannot observe, the guard
now detects the seed banner and exits **`ERROR — nothing was checked`** (exit 2),
never PASS. Absence of a real tool binary is absence of evidence. On this host
today that is what it reports, which is the truthful state: no full-CLI
pure-Simple binary is deployed (see `.claude/rules/commands.md`). The guard goes
live the day one is, with no edit.

### Root cause of the rc=134, corrected 2026-08-23

Not procfs and not a zero-`st_size` read. `std.io_runtime.read_file_text` and
`src/lib/nogc_sync_mut/io/file_ops.spl:76 file_read` were two one-line
forwarders closing into unbounded **mutual recursion** under
last-definition-wins dispatch, so the first read of *any* file aborted the
process. The clamp was simply the first caller on that path to read a file.
Record: `seed_file_read_infinite_recursion_stack_overflow_2026-08-23.md`.

This strengthens rather than weakens the guard's rationale: the failure was a
property of the *deployed build's* dispatch, not of the source, so no
source-level assertion and no unit test of the clamp could have seen it. Only
executing the real command could — which is what the guard does.
