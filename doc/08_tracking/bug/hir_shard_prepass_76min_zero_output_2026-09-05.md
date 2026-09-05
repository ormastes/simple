# HIR shard pre-pass costs 76 min of wall clock and lowers zero modules

**Date:** 2026-09-05
**Area:** `src/app/cli/native_build_main.spl` (`run_hir_shards`),
`src/compiler/80.driver/driver_hir_cache.spl`
**Status:** root cause FIXED for the zero-output half; the cost/benefit half is OPEN

## Measurement envelope

| item | value |
|---|---|
| build | MCP server, 102 units, `--source src/compiler --source src/app --source src/lib`, `--threads 20`, `--cache-dir build/mcp_cache` |
| compiler | Rust seed `src/compiler_rust/target/bootstrap/simple`, sha256 `c855e1e0763034f3...`, 154,557,952 B, mtime 2026-09-05 06:45:58 |
| `bin/simple` | `bin/release/aarch64-unknown-linux-gnu/simple`, 154,560,904 B, 2026-09-04 14:46:17 (probes only) |
| host | aarch64 Ubuntu 24.04, 20 cores, 121 GB; load avg 1.13 |
| source | orchestrator pid 1405707 (start 08:06:25), worker pid 1442263 (start 09:22:50), log `mcpX.log` (16,147 lines) |

Numbers are read from the live build's own log, not re-derived. The 02:03 build
of the same target (`mcp3.log`) shows an identical pattern.

## What was measured

`run_hir_shards` spawns 20 shard children and blocks on `process_wait` for all
of them before the real build starts. That window is **76.4 minutes**
(08:06:25 -> 09:22:50); the shard-phase internal clock agrees at 65.9 min plus
spawn/teardown.

What the 20 shards produced:

```
[hir-shard] done shard=N/20 lowered=0 claimed=0 levels=10     (x20)
[hir-shard] 20/20 shard(s) completed split=queue
```

**Zero modules lowered, zero cache stores.** The real build that followed then
did all the work itself:

```
[frontend-cache] hits=102 misses=0 parses=0
[hir-cache]      hits=0  misses=102 stores=102
```

Cost of the pre-pass: **1,200.7 process-minutes** in `surface_build` alone
(2,060 calls, mean 35.0 s/call under 20-way contention). These are per-process
wall deltas summed across 20 contending processes; on 20 cores that
approximates CPU time but is not measured CPU time.

The phase the pre-pass exists to accelerate is not the expensive one. Main
process, steps 1-4 = 27.7 min:

| phase | wall | share |
|---|---|---|
| `surface_build` (103 calls, 14.3 s/call) | **24.6 min** | 89% |
| `hir` lowering (the shards' target) | **1.7 min** | 6% |
| `parse` (102/102 front-end cache hits) | 1.2 min | 4% |
| `surface_freeze` + everything else | 0.2 min | 1% |

So the pre-pass spends 76 min of wall clock and ~20 CPU-hours to parallelize a
1.7-minute phase — a ratio that cannot pay off even when it works.

## Root cause of the zero output (FIXED)

`hir_cache_has()` tested file EXISTENCE only, while `hir_cache_load()`
additionally validates the entry header. The key folds source + closure
digests; the header additionally folds `frontend_parse_cache_scope()`, which
carries `frontend-exe=<sha256 of the compiler binary>`. **Rebuilding the seed
invalidates every entry without moving any key.**

The seed was rebuilt at 06:45, between the 02:03 build and the 08:06 build,
with the compiler sources unchanged (`sources=5f590...` is identical across
both entry generations on disk). So at the 08:06 build every key still resolved
to an existing file:

- shards: `hir_cache_has(key)` -> true -> skip all 102 as "already cached";
- real build: `hir_cache_load(key)` -> header mismatch -> miss all 102, re-lower
  serially, re-store.

Confirmed on disk: of 216 entries, 114 carried a header from a superseded
compiler identity (`frontend-exe=` values `0eeaf1893db8` x113 and `4e708d1004ae`
x1) against 102 current (`c855e1e07630`, byte-identical to the running seed's
sha256 prefix).

Fixed by making `has` apply the same validity test as `load`. Verified:

```
current-identity entry : OLD has=true   NEW has=true    (genuine hits preserved)
superseded-identity    : OLD has=true   NEW has=false   (the bug)
absent key             : OLD has=false  NEW has=false
```

**Watch the next build.** Every `[hir-cache]` line in both logs reads `hits=0`,
so the HIR cache-HIT branch (`driver_hir_pipeline_lowering.spl:250`,
`hir_stream_cached != nil`) has never been observed running at scale. With this
fix the shards produce entries and the real build will take that branch for up
to 102 modules — the first such run. If a hit skips lowering side effects later
modules depend on (`:463` shared dictionary handle, `:833` "newly lowered traits
remain on the loop-owned lowerer"), the fix would trade slow-and-correct for
fast-and-wrong. Watch `[hir-cache] hits=` and the build outcome on the next run.
This is not a reason to keep `has` and `load` disagreeing — that divergence is
wrong by the module's own contract — but it is not risk-free either.

Also fixed: `_hir_shard_claimed` was incremented only on the queue-claim path,
so a shard using the static split printed `claimed=0` even when it owned
modules. The receipt could not distinguish "owned nothing" from "never counted".

## Still open: the pre-pass cannot pay for itself

The fix makes the shards produce output; it does **not** recover the 76 min. Each
shard re-runs the entire front end to lower its ~5 modules, because **`parse` is
cached but `surface_build` is not** — 24.6 of 27.7 min in the real build, and
~60 min per shard under contention. Verified absent, not merely inferred: no
`surface_cache` / `surface_build_cache` / surface cache-key symbol exists
anywhere under `src/compiler/**/*.spl`.

Two candidate fixes, neither attempted here:

1. **Cache `surface_build`** (the actual 89% cost, and it would speed up every
   build, not just sharded ones).
2. **Gate the pre-pass on measured HIR cost** — skip it when HIR lowering is
   cheap relative to the front end it must redo.

Do NOT simply default `SIMPLE_HIR_SHARDING=0`: `native_build_hir_shard_count`
gates only on that variable, so the bootstrap lane inherits the same pre-pass,
and the "142 s/module interpreted" HIR cost cited in `driver_hir_cache.spl`'s
header for that lane is unverified here. Measure the bootstrap lane before
changing a default that lane depends on.

## Not the cause (checked, ruled out)

- **AST env-mirror** (`decl_nodes.spl` / `nodes.spl` storing AST fields in
  environment variables, an O(n) `getenv` scan per field): gated off on this
  path — `/proc/1442263/environ` has no `SIMPLE_BOOTSTRAP`, so
  `ast_decl_arena_default()` returns arena-preferred. The "interpreter module
  variables may not persist" caveat guarding the slot caches is also stale on
  this seed: a direct probe shows module-level `var`s persist across calls.
- **`[mir-lower]` trace overhead**: `SIMPLE_COMPILER_PHASE_PROFILE` is absent
  from the build's environ. Stage-3-only, not active here.
- **`surface_build` being O(n^2)**: tested per-call `dt` against call index in
  deciles; noisy, 8.0 s -> ~19 s with no clean trend. Not established as
  superlinear — it is expensive per call (14.3 s), not obviously quadratic.
