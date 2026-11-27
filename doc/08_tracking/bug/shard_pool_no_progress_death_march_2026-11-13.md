# Shard pool "death march": no-progress owner deaths dispatch the whole pending queue one identical re-parse at a time

- id: shard_pool_no_progress_death_march_2026-11-13
- status: fixed in source (driver-side, `run_ledger_shards`); takes effect with
  the next self-hosted compiler rebuild (the frozen stage-2 binary keeps the
  old behavior on already-pinned rows)
- severity: P1 (row-level TIMEOUT: a full-CLI stage-2 matrix row burned 3 h
  re-running the identical frontend prologue instead of failing after 30 min)
- found: 2026-11-13, stage-2 bootstrap matrix row `compiler_cli_build`
  (`verification.run4-shard-thrash`, aarch64-apple-darwin, 24 GB host)
- binary: stage-2 capsule sha256 `197b4e93670dd57c9a2da298069ad95b369dc8f75dff57b9a2ced98631c00289`,
  built 2026-11-13 11:53 from `f9dd7ada7645` (git-state-before/after.env)

## Symptom

One `native-build --entry-closure --threads 4 --low-memory` invocation over a
3162-module closure, run under a 13631488 KiB tree cap with row timeout
10800 s, prints five sequential MIR-owner deaths at the 1800 s per-worker
deadline and is then killed by the row timeout during the sixth pass:

```
[mir-shard] shards=8 parallel=1 ledger=.../full-cli/hir/mir-queue-99339-0
[mir-shard] owner=0/8@0 status=TIMEOUT (deadline 1800s) exit=-2 claimed=0 sealed=0 finished=false
[mir-shard] owner=1/8@0 status=TIMEOUT (deadline 1800s) exit=-2 claimed=0 sealed=0 finished=false
[mir-shard] owner=2/8@0 status=TIMEOUT (deadline 1800s) exit=-2 claimed=0 sealed=0 finished=false
[mir-shard] owner=3/8@0 status=TIMEOUT (deadline 1800s) exit=-2 claimed=0 sealed=0 finished=false
[mir-shard] owner=4/8@0 status=TIMEOUT (deadline 1800s) exit=-2 claimed=0 sealed=0 finished=false
... row killed at elapsed_seconds=10801 (status=124)
```

Every owner re-ran `load_sources` (27 s, 4711 files) and the whole phase-2
surface pass from seq=1 (~2389 of 3162 modules per 1800 s) and claimed
**nothing**; the on-disk ledger `mir-queue-99339-0` was empty at the end
(0 claim files, not even an `inventory`). 13212 `phase2:surface:file:parse-done`
events for 3162 modules = ~4 full parse passes in 3 h; the surface commit seq
never got past 2389 in any pass.

## Root cause

`run_ledger_shards` (src/app/cli/native_build_main.spl) is a slot pool: the
inner loop `while next_pending < pending.len() or pids.len() > 0` keeps the
window full, so a reaped owner that died **before claiming anything** merely
frees its slot and the pool immediately spawns the *next pending index*
(driver_hir_recovery.spl:199-201 documents the intent — "a worker that crashed
before claiming anything ... fails only itself"). That intent assumes a
worker dies *after* its cheap prologue; here the assumption inverts:

- Each MIR/HIR shard worker re-parses the **whole closure** by design before
  its first claim (it needs every import surface; the per-file worker holds
  the full HIR). Under this row the prologue alone (load_sources + 3162-module
  parse) exceeds the 1800 s worker deadline, so the parent
  (`hir_shard_reap_deadline_hit_v1` + `process_kill`, still in
  `run_ledger_shards`) kills every worker at claimed=0.
- With `parallel=1` and `count=8` (`SIMPLE_MIR_SHARD_COUNT=8` over a
  memory-admitted single slot), the queue is dynamic: each of the 8 scheduled
  owners starts against a *fully unclaimed* queue and pays the identical
  multi-hundred-second prologue. The failures are deterministic, so owners
  1..7 reproduce owner 0's death exactly — 8 x 1800 s >= row timeout.
- Nothing bounds the *cost* of the march: the claimed=0 death is the one
  shape `hir_shard_recovery_reap_blocks_ledger_v1` deliberately does not
  block on (a no-claim death "fails only itself"), and the existing
  replacement policy (`hir_shard_recovery_can_replace`) never fires because
  it requires `new_claims > 0`. The pool therefore had no early exit between
  "one owner died cheap" and "all 8 owners burned their full deadlines".

The multiplier that pushed the prologue past the deadline: the front-end
parse cache could not store on this row —
`[frontend-cache] store failed: cannot write under .../full-cli/default/frontend
(dir_create_all=true); modules will be reparsed` (8 x; only 1746/3162 warm
hits from the two parse-shard children), so every owner parsed ~2400 modules
in-process instead of promoting cache hits. Store failure is non-fatal by
design (frontend_parse_cache.spl:240-250, "a cache that cannot store is a
slow build, not a wrong one") but it converts one slow pass into five.

## Why run4 was slower than run1

Both rows are the same command with the same stage-2 binary; only the tree cap
differed (run1 11534336 KiB / row timeout 3600 s; run4 13631488 KiB / 10800 s).
The higher cap admitted `available=14898048 kB`, so parse warm-up fanned out to
**2** shard children (`[shard] threads=2`) instead of run1's 1, doubling the
prologue contention on a cold, store-failing cache; run1's single owner got
through all 3162 surfaces plus 1100+ HIR modules in its 1800 s while run4's
owners stalled at seq 2389. run1 was then killed by its own shorter row
timeout right after owner 0's death — same disease, earlier amputation.

## Fix (minimal, driver-side)

`run_ledger_shards` now stops dispatching when an owner dies with
`progress == 0`, unfinished, `total_claims == 0` (no reaped owner ever
claimed) and nothing left live: the queue is then exactly as unclaimed as
before the prologue, so every remaining pending owner can only repeat an
already-failed prologue. The pool drains, prints
`owner=... died before claiming any module ... not dispatching them`, and
exits through the normal aggregate-failure path (code 1). Live owners with
claims and pools where any owner claimed something keep the old behavior, as
do replacement generations (`hir_shard_recovery_can_replace` is untouched).

- src/app/cli/native_build_main.spl: `stop_dispatch` flag (declared with the
  pool state, checked in the slot-pool spawn condition, set in the reap
  chain after the existing block/replace verdicts).

Expected effect on this row: loud `result=FAIL` at ~31 min (one 1800 s
prologue + teardown) instead of `result=TIMEOUT` at 3 h, with the reason in
the log. The MIR fallback policy already refuses the serial retry at
`parallel=1` (`native_mir_shard_fallback_action_v1` requires `parallel > 1`
for `retry-serial`), so no second pass is queued in the observed shape.

The parse-shard layer needed no change: its orphan reclaim is already bounded
to one round (src/app/cli/native_build_main.spl, "One round only").

## Residual risk / follow-ups (not fixed here)

- The underlying capacity problem remains: on a store-failing cache the
  whole-closure prologue exceeds the 1800 s `native_internal_timeout_seconds`
  default, so this row still *fails* after the fix; it just fails fast and
  loud. Durable follow-ups, in impact order:
  1. Why `file_atomic_write` fails under
     `.../full-cli/default/frontend` on this row (dir_create_all succeeded;
     the temp-file/rename step did not — macOS host). Until stores work,
     every owner of every pool re-parses.
  2. A worker-side resume from the committed-surface ledger (phase-2 already
     emits per-file commit seq) would make the prologue incremental across
     owner restarts; that is a driver/runtime change, too large for a release
     branch.
  3. The worker deadline could exclude the pre-claim prologue (or scale with
     closure size) so a slow first claim is not indistinguishable from a hang.
- The stop condition is deliberately conservative (empty ledger + nothing
  live): a claimed=0 death while siblings hold claims, or after any claim was
  recorded, keeps the old march-on behavior. A transient single-startup-crash
  with `parallel>1` and live claimants is unaffected.

## Evidence

- `.../verification.run1-timeout/logs/compiler_cli_build.log` (9.4 MB, row
  killed at 3600 s; 1 owner death; store-failed x2; seq reached 3162)
- `.../verification.run4-shard-thrash/logs/compiler_cli_build.log` (21 MB,
  killed at 10800 s; 5 owner deaths; store-failed x8; max seq 2389/pass;
  `task=compiler_cli_build|result=TIMEOUT|status=124|elapsed_seconds=10801`
  in `summary.env`)
- Empty ledger `.../full-cli/hir/mir-queue-99339-0` (0 entries) after the run
- stage-2 admission: `stage3/aarch64-apple-darwin/stage2-admitted/admission.env`,
  candidate sha256 `197b4e93...`, built from `f9dd7ada7645`
  (`git-state-before.env`, dirty_fingerprint identical before/after)
