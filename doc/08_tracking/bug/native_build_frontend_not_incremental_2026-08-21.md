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
  still runs `flat_ast_to_module`. This was the gate on the whole design and it
  is now **ANSWERED**: the bridge is only 1-4% of per-file cost, so the ceiling
  is ~96%. See Measurement below.
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
**RESULT (2026-08-21): the bridge is only 1-4% of per-file cost. The flat-AST
cache design has a ~96% ceiling and is worth building.**

Measured with `SIMPLE_PARSE_PHASE_PROFILE=1`, the six-phase profile the
parser-perf lane landed in `module_assembly.spl:1058-1088` (which already
supersedes the two markers this record originally asked for). All values are
microseconds, as emitted:

| file | lines | parse_module_body | interp | placeholder | desugar_coll | bridge | total | bridge % |
|---|---|---|---|---|---|---|---|---|
| `driver_types.spl` | 1199 | 66.06 s | 16.07 s | 12.07 s | 0.27 s | **3.90 s** | 98.4 s | **4.0%** |
| `compiler/hir/hir.spl` | — | 0.95 s | ~0 | ~0 | ~0 | **0.025 s** | 0.98 s | **2.5%** |
| `common/driver_core_types.spl` | — | 0.69 s | ~0 | ~0 | ~0 | **0.010 s** | 0.70 s | **1.4%** |

`coverage_inv` is negligible everywhere (tens of microseconds).

Consequences:
- **A flat-AST cache would eliminate ~96% of per-file front-end cost.** The
  non-cacheable half (`flat_ast_to_module`, which still runs on every hit) is the
  small half after all. This removes the doubt that previously gated the design.
- **It is also sound by construction**, which the alternatives are not: a hit
  reproduces the identical `ParserModule`, so surfaces, HIR, and type checking
  all still run normally. It needs no dependency-invalidation prerequisite and
  silences no diagnostics — unlike skipping HIR/MIR on an object-cache hit.
- Secondary finding for the parser-perf lane: on `driver_types.spl`,
  `expand_string_interpolations` (16.1 s) + the placeholder passes (12.1 s) are
  **29%** of the file's cost, versus 67% for `parse_module_body`. Those two
  passes are worth profiling in their own right.
- Also visible via the new `dt=` instrumentation: that 279-file closure spent
  **57.6 s before parse even began** (source load + closure + lint), which is not
  nothing and is not currently attributed to any phase.

### Earlier failed attempts (kept so they are not repeated)
**These external-timestamping routes do NOT work. Use `SIMPLE_PARSE_PHASE_PROFILE=1`
instead — it computes deltas inside the process, so output buffering is irrelevant.**
Three attempts failed, each for a different reason, and the last one is
fundamental:

1. `bin/simple compile <file>` emits no frontend traces at all — `bin/simple` is
   the **Rust seed**, and the interpreted self-hosted frontend only runs under
   `native-build`. Do not use `compile` to probe this path.
2. Piping the run through `awk`/`date` to timestamp lines produced an ordering
   that is physically impossible (every `[flat-bridge]` line apparently preceding
   every `[frontend]` line). That was a stdout-block-buffered / stderr-unbuffered
   interleaving artifact, not real ordering. `stdbuf -oL -eL` fixes the ordering.
3. But `stdbuf` does **not** fix the timestamps, and this is the blocker:
   Simple's `print` goes through the runtime's own internally-buffered writer,
   which `stdbuf`'s libc interposition cannot reach. Only lines explicitly
   followed by `rt_stdout_flush()` — i.e. the `[build]` progress receipts, and
   nothing else — escape promptly. Every `SIMPLE_COMPILER_TRACE` marker sits in
   that buffer until process exit and then arrives in a burst, so an external
   timestamp on it measures the flush, not the work. (This also explains why
   `[build]` receipts stream in a stage log while traces do not.)

Consequence: the split can only be measured from **inside** the process. That is
exactly what `SIMPLE_PARSE_PHASE_PROFILE=1` does, and the numbers above come
from it.

## Moving the object-cache lookup earlier (the highest-value change)

For a cache HIT the step-5 loop consumes almost nothing:
`driver_native_module_cache_source` (`driver_aot_native_output.spl:175-193`)
scans only `ctx.sources` for a path — **available before parse** — and the hit
branch (`:795-806`) just pushes the cached object paths. The only parsed state it
touches is `driver_native_module_is_export_facade(ctx.mir_modules[name],
ctx.modules[name])` (`:390-430`), a "does this module have any code" predicate
that is moot for a module the cache says produced objects.

So the lookup itself can move to right after the source closure. What stops the
front end from being skipped is **dependents**, not the lookup:

- HIR lowering resolves imports against `HirLowering.module_surfaces`
  (`20.hir/hir_lowering/types.spl:65`, read in `_Items/module_import_resolution.spl:238-295`
  and `_Items/module_import_registration.spl:268-477`). A module missing from
  `module_surfaces.index_by_name` fails import resolution in its dependents.
- **No surface can be reloaded from disk.** `ModuleSurface`
  (`20.hir/hir_lowering/module_surface_types.spl:220-285`) is ~30 fields over 8
  nested types and embeds parser `Type`/`Span`/`Variant`/`ParserImport`/`Export`,
  plus real AST bodies in `ModuleSurfaceTrait.default_methods: [ParserFunction]`
  (`:77`, the deliberate "sole executable-body exception") and enum struct-variant
  field defaults. `smf_serialization.spl:212-367` writes bodyless HIR *placeholder*
  records and has no reader, no impls, and no export routes.
  `interface_digest_of` (`cache/action_key.spl:197-204`) and
  `smf_manifest_entry_iface_verdict` (`watcher/smf_manifest.spl:173`) **hash** an
  interface; nothing **reloads** one.

### Ranked options
- **(c) Parse-only for cached deps — ~100-200 lines, recommended first.** Keep
  parse + `ModuleSurfaceBuilder.add_parsed/add_alias`
  (`driver_source_pipeline_parsing.spl:~495-540`) so dependents still resolve,
  but skip **HIR + MIR lowering and codegen** for object-cached modules. Needs a
  skip flag threaded through the HIR/MIR loops plus a synthesized
  `ctx.mir_modules[name]` placeholder for the `:776` dereference. No
  serialization at all. Does **not** reach "parse=0 files" — it reaches
  "HIR/MIR=0 modules".
- **(a) Persist + reload the surface — ~1200-2000 lines.** The only route to
  "parse=0 files". Needs a canon-v1 writer+reader over the nested types above,
  registry re-freeze (`registry_index.spl:200`), and a version/digest guard.
- **(b) Reuse SMF placeholder records — ~600-1000 lines. Not recommended:**
  wrong shape (no impls, no export routes/origins) and write-only today.

### Blocking correctness prerequisite for ALL of the above
`BuildCache.has_cached_object` (`driver_build/incremental.spl:530-545`) compares
**only that one file's own `content_hash`** plus output existence. There is **no
dependency tracking of any kind** — which matches CLAUDE.md's note that
`interface_digest_of` has zero call sites.

Today that is merely wasteful: if `util_a.spl` changes and `main.spl` does not,
`main.spl` hits the cache and its stale object is linked either way. But
`main.spl` is still re-parsed, re-HIR'd and re-MIR'd, so a type error introduced
by the changed interface **is still caught**. Skipping the front end for cache
hits removes exactly that check, turning a wasteful-but-loud build into a fast
and **silent** one. Therefore:

> Moving the lookup earlier MUST land together with dependency-aware
> invalidation, not before it. The cheap sound version is to fold the transitive
> import closure's content hashes into each module's cache key (the fingerprints
> already exist in `BuildCache`), so editing `util_a.spl` changes `main.spl`'s
> key and re-front-ends exactly the affected modules — which is also precisely
> the acceptance criterion for the reproduce spec.

## Progress (2026-08-21)

Landed, in dependency order:
- `58b6bc45e65` codec primitives + round-trip spec (12/12 green). Six element
  types cover all 151 pools. Fails closed on truncated/negative/absurd length
  headers. The spec caught a real defect on its first run (`to_i64()` parses,
  it does not return a character code).
- `6c29dccc915` `scripts/check/check-flat-ast-codec-complete.shs` — derives the
  pool list from source on every run so a pool added tomorrow is covered the day
  it lands. 5 fatal selftest fixtures; 0 pools is ERROR. It caught its own
  author's stale exclusions immediately.
- `98af874928a` dump/restore for all **151/151** pools. Guard green. A full
  dump -> restore -> dump cycle returns `ok=true stable=true`; the fixture
  native-build still exits 0.

**Measured cost of the codec source itself: +18.1s (+19.6%)** on the 3-module
fixture build (92.3s -> 110.3s, same tree, same binary, only the change
toggled). ~500 added lines in four files the compiler re-parses on every process
start. This is a transitional cost of source-read compiler layers, not of the
design, and it is repaid many times over once the cache is wired — but until
then it is a real regression for short one-off invocations and must not be
cited as free.

Still to do: the full-closure round-trip gate (parse a real module, dump, reset,
restore, rebuild through the bridge, compare), the cache wiring at the `:379`
hook, and parse sharding across `--threads` worker processes.

## NEXT STEP (deferred, do not start before the prerequisite)

Moving the object-cache lookup earlier — so an unchanged module skips
parse/HIR/MIR entirely — is **deferred until transitive dep-hash keying
exists**, per the correctness prerequisite above. `BuildCache.has_cached_object`
today compares only the module's own content hash, so skipping the front end
would silence type errors that a changed dependency interface currently still
surfaces. The cheap sound version is to fold the transitive import closure's
content hashes into each module's cache key using the fingerprints `BuildCache`
already holds; that is also exactly what makes "edit one file -> re-front-end
that module and its affected dependents" true rather than approximate.

## Status
**Not fixed.** Instrumentation only (`146d987b1c0`). The front-end cache and the
parse sharding are designed and sited above but not implemented: the codec must
live in `src/compiler/10.frontend/core/**`, which was out of scope for this
session, and the parse-vs-bridge split that gates the design's value was still
being measured when the session ended. **Recommended order, REVISED by the 1-4% bridge measurement.** The flat-AST
cache should come FIRST, ahead of moving the object-cache lookup earlier:

1. **Flat-AST per-module cache** (~700-1000 lines + round-trip gate). Highest
   value and *lowest risk* of the three: ~96% of per-file front-end cost, and
   sound by construction because a hit rebuilds the identical `ParserModule`, so
   HIR and type checking still run and no diagnostic is silenced. Land the codec
   alone first, gated by round-trip equality over the whole `src/app` closure,
   before wiring any cache or shard mode.
2. **Then** the per-module cache wiring at the `:379` hook, and sharding.
3. **Only then** skipping HIR/MIR on an object-cache hit — and only together
   with dependency-aware invalidation, per the prerequisite above. It is the
   riskiest of the three and, now that parse can be made ~25x cheaper, no longer
   the biggest win.

