# native-build HIR-shard stall recovery: bounded per-shard waits, kill, claim reclaim, retry, degrade

- **Filed/fixed:** 2026-09-18
- **Status:** FIXED — exercised live across three Windows builds
  (nb10: 5/10 shards timed out and the build CONTINUED; nb17/nb18: full
  timeout waves recovered). Previously one stalled shard held the whole build
  hostage.

## Symptom (pre-fix)

`native-build` on Windows reached the HIR shard fill and, on the first bad
shard, emitted nothing further for hours. Killing the stalled worker failed
the whole build with "worker exited with code 1" and no diagnosis.

## Root cause

`run_hir_shards` (src/app/cli/native_build_main.spl) waited each shard with the
whole-worker budget (`DEFAULT_TIMEOUT_MS` = 6h) and:

- counted a non-zero wait result but printed nothing (silent),
- never killed a timed-out child (a wait timeout returns while the child is
  still alive, burning a core and holding its queue claims),
- never released queue claims, so the modules a dead shard claimed were
  skipped by everyone and surfaced later as `MIR lowering missing HIR module`
  against an innocent importer,
- had no retry: one pathological shard = a wasted day.

The parse-shard lane right above it (`run_parse_shards`) already had the
correct pattern: per-shard status lines, release-claims + one retry round,
degrade-to-inline on a second death.

## Fix (mirrors the parse lane)

- `hir_shard_wait_ms(count, timeout_ms)`: per-shard budget with a 2h floor
  (cold-pipeline shard children re-run parse+surface themselves, ~1.5-3.5h
  interpreted; a tight floor kills them mid-surface — observed 2026-09-17
  with a 30-min floor: 5/10 shards timed out during surface_build).
  Override: `SIMPLE_HIR_SHARD_WAIT_MS`.
- `spawn_hir_shards`: bounded wait, per-shard `FAILED <label>` status,
  `process_kill` on timeout/death, `parse_shard_release_claims` so a retry
  shard (or the real build's own lowering) picks the orphans up.
- Deadline accounting across the sequential waits: all shards spawn together
  and share ONE budget window; each wait uses `remaining = budget - elapsed`
  (+30s reap grace) instead of a fresh full budget per shard. Sequential
  full-budget waits cost N x budget (observed 2026-09-18: 4 shards x 3h).
- One reclaim round; a second death degrades to the real build lowering the
  remainder inline (modules with no HIR cache entry are lowered by the real
  build — measured fast for ~805/813 modules in nb10).

## Evidence

- nb10 (2026-09-17): shards 0-4 TIMEOUT at the then-30-min floor (killed
  mid-surface), 5-9 exit=0, build continued; real worker lowered 805/813 hir
  modules inline in minutes.
- nb17/nb18 (2026-09-18): full 4/4 timeout waves recovered cleanly; the
  deadline accounting collapsed the phase to ~budget + N x grace.

## Remaining debt (separate row)

The reason shards keep timing out is that each shard child re-runs the whole
pipeline through surface (no surface cache exists) — ~4h at 4-way parallelism,
over any sane per-shard budget. A surface-result cache, or letting shard
children share the coordinator's surface, would make the fill actually fill.
Also the underlying HIR-tail memory accumulation
(`native_build_interpreted_worker_rss_blowup_2026-08-18.md` family) still
bounds full builds on <=64GB hosts.
