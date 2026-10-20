# Stage 3 HIR cache: the direct route misses every entry the sharded route stored

- Status: OPEN
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2 (each route change re-lowers the whole closure: ~50 min)

## Observation

Same output dir and HIR cache dir
(bootstrap-r16b/stage3/aarch64-unknown-linux-gnu/stage3-native-cache/hir):

1. Sharded route (8 HIR workers, snapshot source roots) stored entries for
   its 2280-module closure.
2. Direct route resume (1352 modules, a subset of those files) reported
   `[hir-cache] hits=0 misses=1352 stores=1352`.

The direct route found none of the files the sharded workers stored, so the
cache key differs between the routes for the same source file (candidates:
snapshot vs checkout path, closure/provider set, worker identity).
