# Stage 2 reuse run: HIR shard cannot create invocation ledger in sealed stage2-native-cache (EACCES)

Date: 2026-10-31
Host: Linux aarch64, 20 CPUs, 121 GiB RAM
Lane: stage2 trust-root bootstrap, `--full-bootstrap --stop-after-stage2 --backend=cranelift --jobs=half`

## Symptom

Second consecutive run of the same bootstrap lane (retry 3, reusing the retry-2
stage2 native cache without `--invalidate-cache`) aborts at the struct
receiver / runtime-capability step before the phase-verification matrix starts:

```
error: Stage 2 struct receiver/runtime capability failed
    | [hir-shard] ERROR: cannot create invocation ledger directory
      '/home/yoon/dev/simple/.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-native-cache/hir/queue-2635951-0'
      (selected by ambient SIMPLE_HIR_CACHE_DIR)
    [hir-shard] BLOCKED: cannot establish invocation ledger
    error: HIR aggregate failure; final worker and artifact publication blocked
    error: stage2 receiver compilation failed with status 1
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

Primary evidence: `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-receiver.log`.

## Root cause

The retry-2 run published `stage2-native-cache/` sealed read-only
(`.bootstrap-cache-binding` mode `0400`, directories `dr-x------`, observed
2026-10-31 12:23). On the retry-3 run the cache is content-compatible, so the
lane reuses it — but the struct-receiver step still needs a writable HIR
invocation ledger and selects the sealed cache's `hir/` directory through the
ambient `SIMPLE_HIR_CACHE_DIR` (`src/compiler/80.driver/driver_hir_cache.spl:133`).
`mkdir hir/queue-<pid>-0` fails with EACCES and the shard blocks the whole
receiver compilation.

So the read-only sealing that protects a *published* cache is not lifted (and
the queue is not redirected to a writable lane-owned directory) on the
cache-reuse path. Cold runs never hit this because the cache is writable until
publication.

## Repro

1. Run `bash scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
   --stop-after-stage2 --backend=cranelift --jobs=half` to stage-2 publication
   (any later abort is fine — e.g. the rss-cap-exceeded exit 88 of retry 2).
2. Re-run the same command without `--invalidate-cache=stage2`.
3. Observe the EACCES ledger failure at the struct receiver step.

## Workaround used

Retry 4 passes `--invalidate-cache=stage2` (accepts the ~13 min cold rebuild) —
verified to get past the receiver step (retry 2 proceeded from the same state
into the phase-verification matrix).

## Suggested direction

Either (a) re-open the cache's `hir/` subtree (`u+w`) before steps that need a
ledger and re-seal at the end, or (b) point the ambient `SIMPLE_HIR_CACHE_DIR`
for receiver/capability steps at a lane-owned writable queue root instead of
the sealed published cache. Keep the publication sealing intact for true
consumers.

**Status:** OPEN
