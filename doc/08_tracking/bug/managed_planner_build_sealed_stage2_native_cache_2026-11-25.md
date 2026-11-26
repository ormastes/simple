# Managed planner build fails on warm rerun: SIMPLE_HIR_CACHE_DIR points into sealed stage2-native-cache (2026-11-25)

Status: FIXED by PR #11605 (option 1: `adm_run_planner_build` exports
`SIMPLE_HIR_CACHE_DIR="$adm_dir/planner-hir-cache"`). The local chmod
workaround applied to pinned-e803fa9762cd is retired: that pinned tree was
superseded by pinned-008177e5a830 (lane v7, 2026-11-26) and is no longer
used by any lane, so there is nothing left to re-seal.
Lane: `--full-bootstrap --stop-after-stage2 --produce-managed-receipt=self-host-convergence-check`
on release/1.0.0 @ e803fa9762c (aarch64-unknown-linux-gnu, llvm)

## Symptom

Second (warm-cache) run of the Stage 2 trust-root lane on the SAME pinned
output aborts after a successful Stage 2 admission:

```
bootstrap-admission-error: planner-build-failed
error: could not produce the managed Stage 4 planner admission
```

`admission/<key>/__bootstrap_stage4/planner-build.log` shows:

```
[hir-shard] ERROR: cannot create invocation ledger directory
  '.../stage3/<triple>/stage2-native-cache/hir/queue-<pid>-0'
  (selected by ambient SIMPLE_HIR_CACHE_DIR)
error: per-file worker pool ledger directory unavailable; no fallback
```

## Root cause

The first successful run seals `stage2-native-cache` (and `hir/`) read-only
(`dr-x------`) when Stage 2 admission completes. On a warm rerun, the
managed Stage 4 planner build (`produce-bootstrap-planner-admission-v2.shs`,
`adm_run_planner_build`) inherits the wrapper's ambient
`SIMPLE_HIR_CACHE_DIR=.../stage2-native-cache/hir` and the per-file worker
pool tries to create its invocation ledger (`queue-<pid>-N`,
`mir-queue-<pid>-N`) inside the sealed directory → EACCES → planner build
fails. The cold path never sees this because the seal happens after the
first planner build.

## Workaround (applied 2026-11-25, retired 2026-11-26)

`chmod -R u+w <output>/stage3/<triple>/stage2-native-cache` before the warm
rerun. Content was untouched (mode bits only); the worker-pool ledger dirs
are transient. No longer needed: the harness fix makes the planner build
write its ledger outside the sealed cache, and the affected pinned tree is
out of service.

## Proper fix (landed, PR #11605)

The planner build must not write into the sealed stage2 cache. Either:

1. `produce-bootstrap-planner-admission-v2.shs` overrides
   `SIMPLE_HIR_CACHE_DIR` (and the MIR queue parent) to a scratch dir under
   the admission workdir for `adm_run_planner_build`, or
2. the wrapper unsets the ambient `SIMPLE_HIR_CACHE_DIR` before invoking the
   producer.

Option 1 is narrower and keeps stage2-build behavior unchanged.

## Repro

1. Run the trust-root lane to a successful Stage 2 admission (seals the
   cache).
2. Re-run the identical command against the same pinned output.
3. Stage 2 rebuild reuses the cache (PASS), admission re-runs, planner build
   fails as above.
