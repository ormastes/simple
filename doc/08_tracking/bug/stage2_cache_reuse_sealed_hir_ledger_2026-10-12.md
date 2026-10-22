# Stage2 cache reuse lane blocked by admission seal ordering (2026-10-12)

Status: OPEN (P1). Blocks warm-cache step-1 reruns; workaround is
`--invalidate-cache=stage2` (full rebuild) for every cycle.

## Symptom

Two step-1 cycles with cache REUSE (cycle 14, cycle 17) died at the SAME gate:

```
Stage 2: proving struct receiver/runtime capability
[hir-shard] BLOCKED: cannot establish invocation ledger
error: HIR aggregate failure; final worker and artifact publication blocked
error: stage2 receiver compilation failed with status 1
VERDICT — ABORTED: stage=stage2 exit=3
```

Cycles with `--invalidate-cache=stage2` (13, 15) pass this gate.

## Root cause chain (evidence)

1. Stage 2 admission seals the live native cache read-only:
   `bootstrap-from-scratch.sh:4610` `chmod -R a-w "${stage2_cache_absolute}"`,
   which runs BEFORE the compiler-test phase in the same run (comment at
   :4621 documents the seal-then-test ordering).
2. The compiler-test phase (and the receiver probe in particular) runs the
   admitted candidate with `SIMPLE_HIR_CACHE_DIR=${stage2_cache_absolute}/hir`
   (`bootstrap-from-scratch.sh:3983,4134,5062`).
3. The candidate's HIR shard driver creates its invocation ledger (transient
   `queue-{pid}-{n}` dirs) UNDER that cache dir
   (`src/app/cli/native_build_main.spl:805` — returns "cannot establish
   invocation ledger" when `dir_create_all` fails).
4. Verified on disk after cycle 17:
   `stage2-native-cache` and `stage2-native-cache/hir` are `dr-x------`
   (sealed), with a stale `hir/queue-2059141-0` from the sealing run.

On a FRESH cache the seal has not happened yet when the receiver probe runs,
so the queue dir creates fine. On REUSE the cache is already sealed from the
previous admission, so every reuse lane fails at the receiver gate.

Related: the same seal-vs-reuse disease family as
`fix(bootstrap): replace stale read-only target-c-inputs binding across
campaigns` (39c6231e417, 2026-10-12) — evidence finalization chmods shared
directories read-only and later reuse phases need to write transient state
into them.

## Candidate directions (not yet implemented)

- Move the HIR invocation ledger out of the sealed cache (e.g. a writable
  per-invocation tmp root selected by the candidate when the cache root is
  not writable), or
- Re-open the cache owner-write for the compiler-test phase and re-seal
  after, or
- Seal only after the compiler-test phase publishes.

Each changes admission/evidence ordering and needs campaign review.

## Workaround

Always pass `--invalidate-cache=stage2` for `--stop-after-stage2` cycles
that include the compiler-test phase. Warm reuse is not currently usable.
