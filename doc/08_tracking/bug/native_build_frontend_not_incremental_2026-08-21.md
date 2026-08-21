# native-build front end is neither incremental nor parallel (2026-08-21)

## Symptom
A self-hosted `native-build --entry-closure` stage build spends the bulk of its
wall clock in phase 1/6 (`parse`), single-threaded, and **repeats all of it on
every rerun even when not one source byte changed**. Stage 1 over `src/app`
parses 662 files serially. A one-file edit costs a full reparse of all 662.

Observed live during this investigation (stage-1 lane,
`/mnt/data/seedperf/simple.v2 native-build`): `[build] parse 220/662 step 1/6`
still climbing after the run had been going for a long stretch.

## Root cause (three separate facts, all verified)

### 1. `--threads` never reaches the front end
`--threads N` is parsed at `src/app/io/_CliCompile/compile_targets.spl:891-907`,
exported as `SIMPLE_NATIVE_BUILD_THREADS` (`:1131`), and read back by
`driver_native_build_threads()` at
`src/compiler/80.driver/driver_aot_native_output.spl:129-135`. Its **sole**
consumer is `ParallelBuildConfig(num_threads: ...)` at `:860`, i.e. the native
CODEGEN/LINK job (`driver_build/parallel.spl:83,128-130`). Nothing in parse or
HIR reads it. The parse loop
(`driver_source_pipeline_parsing.spl:361`, `for source in unique_entry_sources:`
-> `parse_full_frontend(...)` at `:379`) is serial by construction.

### 2. No parse or HIR output is cached at all
Only OBJECT files are cached. There is no per-module cache of parse or HIR
output anywhere on this path. `driver_build/incremental.spl` is fingerprint +
object-path bookkeeping (`BuildCache`, `FileFingerprint`).
`80.driver/incremental_builder.spl` is a standalone prototype
(`IncrementalState` / `CachedArtifact`) that the native-build driver never
references. `.smf` artifacts (`driver_aot_smf_output.spl`,
`watcher/smf_manifest.spl`) are the daemon/interpret path, not native-build.
`hydration_manifest.spl` is unrelated (WASM/DOM hydration manifests).

### 3. An object-cache HIT still pays full parse + HIR + MIR
This is the headline, and it caps what the existing cache can ever buy. The
object-cache lookup (`build_cache.get_cached_outputs` at
`driver_aot_native_output.spl:782`, scope-filtered at `:420`/`:784`, hit at
`:795`) runs in step **5/6**, iterating `module_names` drawn from
`ctx.mir_modules`. Everything upstream — parse (1/6), HIR (2/6), MIR (4/6) —
has already run for every module by then. A 100%-hit rebuild therefore still
pays the entire front end and only skips codegen. That is why the object-cache
persistence fix landed earlier today did not make a rerun fast.

## What blocks the obvious fix, and what does not

A prior note,
`doc/05_design/compiler/incremental_build/parse_phase_process_sharding_blocked_2026-08-21.md`,
concluded that sharding/caching was blocked because there is no serialized form
for a parsed module: `ParserModule` is ~25 collections over 72 struct/enum/class
types with 148+ expr variants, and `smf_serialization.spl` is signature-level
only. **That conclusion is correct about `ParserModule` and is hereby refined,
not overturned: a `ParserModule` codec is still not the right boundary.**

The boundary that IS viable is one layer lower — the core parser's **flat AST**:

- `parse_and_build_module_scoped`
  (`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1038`) is two
  halves: `parse_module_body()` + interpolation/placeholder/collection desugars,
  which fill global flat pools, then `flat_ast_to_module(path)` (`:1080`), the
  3382-line bridge that materialises the rich `ParserModule`.
- The flat pools are **scalar-only and therefore dumpable**: ~120 module-level
  `var` arrays of `i64` / `text` / `bool` / `[[i64]]` / `[[text]]` (one
  `[[[text]]]`, `decl_type_param_constraints`), across
  `core/_Ast/decl_nodes.spl:245-321,1239-1250,1309-1311,1349-1351` (~60 vars),
  `core/_AstExpr/nodes.spl:85-102,805-814` (34), `core/ast_stmt.spl:43-57,532-533`
  (18), and `core/types.spl` (50, enumerated exactly by `reset_all_pools()` at
  `core/types.spl:1455-1503`). Every cross-reference is an integer index into a
  sibling pool. No structs, classes, or enums appear in a pool.
- The pools are reset per file (`reset_all_pools()` at `module_assembly.spl:1041`,
  `ast_reset()` at `:1082`), so indices are self-consistent within one module.
  A cache hit means: reset, refill pools verbatim, call `flat_ast_to_module(path)`.

So the missing piece is a flat-pool dump/restore (~700-1000 lines, plus ~200 if
restore goes through the existing `*_set` helpers), **not** a `ParserModule`
codec of several thousand.

### Two caveats that must not be skipped
- **The bridge half is not cacheable by this design.** A flat-AST cache hit
  still runs `flat_ast_to_module`. If the bridge is the dominant half of per-file
  cost, the cache's ceiling is low. Measuring this split is the gate on the whole
  design (see Measurement below).
- **Dual store under `SIMPLE_BOOTSTRAP`.** decl/stmt/expr pools mirror into env
  vars (`decl_nodes.spl:154-200`, `ast_decl_prefer_arena` /
  `ast_decl_env_mirror_enabled`). A restore must either run arena-preferred or
  replay through the setters, or the mirror goes stale.
- Risk to respect: with ~120 pools, **every omitted pool is a silent miscompile
  of the bootstrap compiler**, not a loud failure. Any codec must land behind a
  round-trip equality gate over the whole `src/app` closure before it is trusted.

## Hook sites (for whoever implements this)
- Skip-parse on hit: immediately before `parse_full_frontend` at
  `src/compiler/80.driver/driver_source_pipeline_parsing.spl:379`. A hit must
  supply both the `ParserModule` box pushed at `:415` and the module surface
  built at `:505-510` — HIR needs surfaces for **all** modules simultaneously
  (`driver_hir_pipeline_lowering.spl:94`), though it does not need all full ASTs.
- Streaming lane equivalent: `parse_all_streaming_surfaces_in_place_impl`,
  `driver_source_pipeline_parsing.spl:175-287`.
- Cache scope: reuse `native_build_cache_scope_key` /
  `native_build_cache_lane()` (`driver_build/incremental.spl:197,192`), which
  already honour `SIMPLE_CACHE_SCOPE`.
- Sharding: `src/app/cli/native_build_worker.spl` is a 29-line passthrough
  (guards `SIMPLE_NATIVE_BUILD_WORKER==1`, forwards argv to `cli_native_build`),
  spawned by `run_native_build_worker` (`src/app/cli/native_build_main.spl:266-287`).
  It accepts the whole CLI arg set; there is **no** module-subset/shard flag yet.

## Measurement

### Instrumentation landed (commit `146d987b1c0`)
Before this, the parse phase emitted one `[build]` receipt per file with **no
timestamps**, so per-file cost could only be recovered by sampling the stage log
from outside with `date(1)`. Every `[build]` line now carries
`+<total>ms dt=<since-previous>ms`, and the `SIMPLE_BUILD_PROGRESS_EVENTS` sink
carries `elapsed_ms=` / `dt_ms=`. `current=` remains the last field and nothing
parses this line, so positional consumers are unaffected.

Example (3-module fixture, per-file parse cost now self-reporting):
```
[build] parse 1/3 step 1/6 +85ms  dt=56ms .../main.spl
[build] parse 2/3 step 1/6 +112ms dt=27ms .../util_a.spl
[build] parse 3/3 step 1/6 +151ms dt=38ms .../util_b.spl
```

### Parse-vs-bridge split
Measured with `SIMPLE_COMPILER_TRACE=1`, which already emits all three needed
boundary markers with no source edits:
`[frontend] parse_and_build:start` -> `[flat-bridge] path=` (start of
`flat_ast_to_module`) -> `[frontend] parse_and_build:done`.

Note for anyone repeating this: **`stdbuf -oL -eL` is mandatory.** Without it
stdout is block-buffered while stderr is not, and the markers interleave out of
order — a first attempt showed every `[flat-bridge]` line apparently preceding
every `[frontend]` line, which is a buffering artifact, not a real ordering.
Also note `bin/simple compile` does **not** exercise this path at all: `bin/simple`
is the Rust seed, and the interpreted self-hosted frontend only runs under
`native-build`.

Result: PENDING — see Status.

## Status
**Not fixed.** Instrumentation only (`146d987b1c0`). The front-end cache and the
parse sharding are designed and sited above but not implemented: the codec must
live in `src/compiler/10.frontend/core/**`, which was out of scope for this
session, and the parse-vs-bridge split that gates the design's value was still
being measured when the session ended. Implement in this order:
1. Measure the split. If the bridge dominates, this design is not worth 1000 lines.
2. Land the flat-pool codec alone, gated by round-trip equality over the whole
   `src/app` closure, before any cache or shard mode is wired.
3. Then the per-module front-end cache at the `:379` hook.
4. Then `--parse-shard i/N` in `native_build_worker.spl` + parent fan-out.
