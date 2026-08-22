# Compiler / interpreter memory retention — measured survey

Date: 2026-08-21
Area: `src/compiler_rust` (seed), `src/compiler/80.driver` (pure-Simple driver)
Status: PARTIALLY RESOLVED — census gap fixed; three of four hypothesised
defects measured and REFUTED; one real retainer identified and filed below.

## Summary

This record exists because three hypothesised memory defects were handed over as
known-bad. Measured on the deployed seed `5020e8f3f45`, **two of the three are
already fixed** and a third never existed. The one real, unexplained retainer is
named in "Open" at the bottom. Numbers first, so the refutations are not taken on
assertion.

## Measurements

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
(60214744 bytes, 2026-08-21 20:20:05), seed `5020e8f3f45`. Shared box under
concurrent load from other lanes, so wall times are an envelope, not a floor.

| run | command | peak RSS | wall |
|---|---|---|---|
| (a) | `lint src/compiler/80.driver/driver_types.spl` (JIT) | **0.44 GB** | 15.2s |
| (b) | same + `SIMPLE_EXECUTION_MODE=interpret` on `50.mir/_MirLoweringExpr/switch_operators_calls.spl` | **0.69 GB** | 338s |
| (c) | stage1 `native-build --threads 1`, parse phase | **1.53 MB/module, linear** | — |

### (a) and (b) are already fixed, not open

The brief carried (b) as "12-13.6 GB". It measures **0.69 GB** — a 19x
improvement — because `e73a0bec647` removed the per-call env-rebuild mechanism.
The census confirms the mechanism is gone rather than merely cheaper:
`captured_env_with_live_globals: calls=0`. That is the answer to the OPEN root
cause in `seed_interp_env_template_cache_unbounded_2026-08-21.md` ("the cloned
Env's Arc graph is retained elsewhere"): there is no longer a cloned Env graph to
retain, so the question is moot. That record is updated accordingly.

**Method warning that cost a measurement here:** `SIMPLE_EXECUTION_MODE=interp`
is NOT a recognised value — the accepted spelling is `interpret`. The invalid
value silently falls back to JIT and reports 0.86 GB / 15.4s, which is a JIT
number wearing an interpreter label. The tell was that it matched run (a)'s wall
time almost exactly. Anyone re-running (b) must use `interpret` and should expect
~338s, not ~15s.

### (c) parse retention is ~0.95 MB/module and LINEAR — not 40 MB/module

Sampled `/proc/<pid>/status` VmRSS every 30s against the `[build] parse N/667`
counter, `--threads 1`, `SIMPLE_CACHE_SCOPE=mem`:

| modules parsed | RSS |
|---|---|
| 196 | 0.189 GB |
| 247 | 0.228 GB |
| 283 | 0.277 GB |
| 336 | 0.322 GB |
| 351 | 0.362 GB |
| 431 | 0.548 GB |

Linear, but measure the slope over the WIDE window, not the first few samples:
196 -> 431 is 235 modules for 0.359 GB = **1.53 MB/module**. (The first four
samples alone give 0.95 MB/module; that early figure understates it and should
not be quoted. The recorded budget of 2.0 MB/module is set against 1.53.)

Extrapolated to 667 modules that is **~0.9 GB at end of parse**, not 3.7-5.3 GB.
The run was stopped at 431/667 to free host memory, so the endpoint is an
extrapolation from a straight line, not a measurement — stated as such.

So the reported 3.4-5.3 GB shard-worker RSS is **not** explained by per-module
parse retention, and the "~40 MB per module in a shard" figure does not hold for
the parse phase. Whatever produces multi-GB shard workers happens in HIR/MIR, or
scales with thread count, not in parse. This is the open item.

### Zero-slack allocation growth: REFUTED

Hypothesis (iii) was that `rt_array_push` / `rt_string_*` realloc exact-size and
so never reuse freed blocks. The C runtime already grows by **doubling**
everywhere it grows: `src/runtime/runtime_native.c:6979-6982` (array grow,
`new_cap *= 2`), `:2607-2609` (byte builder), `:1298-1301`, `:1853`, `:6127`.
There is no exact-size growth path to fix.

### Driver-level eviction: already implemented, and reclaims zero

Hypothesis (i) was that the driver holds sources + flat pools + ParserModule +
HirModule simultaneously and should drop them. It already does drop them:
`CompileContext.evict_sources()` / `evict_ast()` / `evict_hir()`
(`src/compiler/80.driver/driver_types.spl:1096,1130,1134`), called from
`driver_hir_pipeline_lowering.spl:305-307`, `driver_orchestration.spl:154-161`,
`driver_aot_native_output.spl:803,929`. Flat pools and token vectors are already
released per file via `driver_end_transient_parse_scope()`
(`driver_source_pipeline_parsing.spl:148-175`), and the front-end cache already
persists the pools to disk (`10.frontend/frontend_parse_cache.spl`), so the
in-memory copy is genuinely redundant and genuinely dropped.

**But the drops reclaim nothing**, and this is already documented in the source
at `driver_types.spl:1110-1129`: they drop references only, and with no GC and no
refcounting that frees 0 of 2001 allocations (probe P0,
`src/runtime/test/rt_driver_eviction_reclaim_selfcheck.c`). `rt_dict_free_deep`
was measured as a fix and is worse — class instances are untagged header-less
`rt_alloc` blocks, so the planner treats each module object as a LEAF and frees
only key strings that are aliased from outside the dict (probes P2/P3).

Making these evictions actually reclaim requires class instances to be
identifiable at runtime — a codegen/representation change, not a driver change.
That is out of scope under the standing constraint against architecture changes.
Tracked at `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`.

## Fixed here: the census never reported on the paths worth profiling

`SIMPLE_MEM_TRACE=1` is documented as the in-process profiler (ptrace attach is
blocked on these hosts: `ptrace_scope=1`, `perf_event_paranoid=4`). It was
effectively dead: the only caller of `mem_trace::report` was `clear_module_cache`,
which neither `lint` nor `native-build` reaches. Measured before the fix:
`SIMPLE_MEM_TRACE=1 simple lint driver_types.spl` printed **0** `[mem]` lines on
the JIT path and 1 on the interpret path.

Fix: `mem_trace::ExitReport` (RAII, `mem_trace.rs`) installed at the top of
`real_main()`, plus an explicit `report("process exit")` before the terminal
`process::exit` in `driver/src/main.rs`. The explicit call is required because
`process::exit` does not run destructors, so the guard alone would never fire on
the dominant CLI path. Installed on the `simple-main` thread specifically,
because `MODULE_COSTS` / `PHASES` are thread-local.

Default off; costs one env lookup at exit when unset. Mechanism test: `[mem]`
line count on run (a) goes **0 -> 36**. Peak RSS unchanged (451 MB -> 453 MB),
i.e. the instrument does not perturb the thing it measures.

## ANSWERED 2026-08-21: where the parse shard's other ~3 GB is

The apparent contradiction — a `[parse-shard]` worker handling ~80 files sits at
3.4-3.6 GB, while measured parse retention is 1.53 MB/module (~120 MB for a
shard) and a base `lint` process is 0.44 GB — is resolved. **There is no
contradiction, because the 3 GB is not retention at all.**

Probe: 2-shard build, `--threads 2`, `SIMPLE_CACHE_SCOPE=memshard`,
`SIMPLE_MEM_TRACE=1`, seed `/mnt/data/seedperf/simple.mem`.

**It is a fixed startup cost, not accumulation.** Both shards reached 3.35 GB
within 45 seconds of launch, and RSS then stayed FLAT while the parse counter
went from 63 to 467:

| parse lines emitted | shard 0 RSS |
|---|---|
| 63 | 3.36 GB |
| 221 | 3.42 GB |
| 319 | 3.33 GB |
| 467 | 3.37 GB |

Flat within noise. That alone refutes two of the four hypothesised candidates:
sources + flat pools for all 667 modules, and front-end cache blobs kept after
write, would both grow as parsing proceeds.

The census attributes it exactly. Per shard process at exit:

```
[mem] process exit live=2431.6MB peak=2997.7MB rss=3466.5MB
      allocs=399320094 total_alloc=70022.8MB
[mem] phases: module_loads=662 source=11.0MB ast_items=15952
      parse_retained=391.2MB eval_retained=2102.8MB
      parse_bytes_per_source_byte=35.6 env_entries=949861
[mem] globals census: module_envs=667 import_bindings=927167
```

**`module_loads=662` and `module_envs=667` in a shard that parses ~80 files.**
Every shard loads and evaluates the entire compiler closure, because each shard
IS a full compiler instance — the seed running the pure-Simple compiler. The
breakdown of the 3.35 GB:

- **`eval_retained` = 2.10 GB** — dominant. Loading/evaluating all 662 compiler
  modules.
- `parse_retained` = 0.39 GB.
- 927,167 import bindings and 949,861 env entries, versus 48,646 / 53,227 in a
  base `lint` process — **19x**, which is the whole difference between 0.44 GB
  and 3.35 GB.

The shard's own ~80 files of work is a rounding error on top of this.

**Not fixed here, and it is not a retention bug.** Nothing is being held past
its usefulness: the shard needs the compiler loaded in order to be a compiler.
The waste is structural — 8 shards x ~2.5 GB of *identical* compiler closure is
~20 GB of the ~27 GB an 8-way build costs, duplicated once per process. Removing
it means sharing one loaded closure across shards (threads rather than
processes, or a shared/`fork`-inherited image), which is an architecture change
and is out of scope under the standing constraint.

The cheap operational lever, available today with no code change: **shard count
costs ~2.5 GB of fixed overhead each**, so the RSS of a build is roughly
`0.9 GB + 2.5 GB x threads`. Choose `--threads` against available memory, not
against core count.

## Open: per-module env/export materialisation

With the census working, run (a) attributes retention to per-module environments
rather than to AST:

```
[mem] phases: module_loads=161 source=2.3MB ast_items=5414
      parse_retained=91.7MB eval_retained=156.5MB
      parse_bytes_per_source_byte=40.6
      env_entries=53227 export_entries=53458
[mem] globals census: flat=718 owners=84 owned_entries=721
      module_envs=161 import_bindings=48646
```

- Parse retains **40.6 bytes per source byte**.
- 161 module envs hold **53,227 env entries** and **48,646 import bindings** —
  roughly 330 env entries and 300 import bindings *per module*.
- Worst single module: 29,674 B of source retaining **8.29 MB self** with 2,427
  env / 2,412 export entries. Retention tracks env width, not source size.

That is O(modules x visible globals) materialisation: each module env
re-materialises the bindings it imports instead of sharing them. It is the
largest single retainer the census can see, and it is the most likely candidate
for the unexplained multi-GB shard workers. Deduplicating or sharing import
bindings across module envs changes how a phase materialises its environment, so
it is a design change and is filed rather than attempted here.

## Reproduce

```bash
SIMPLE_MEM_TRACE=1 /usr/bin/time -v bin/simple lint src/compiler/80.driver/driver_types.spl
SIMPLE_MEM_TRACE=1 SIMPLE_EXECUTION_MODE=interpret /usr/bin/time -v \
  bin/simple lint src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl
```

## FIXED 2026-08-22: parse-shard workers no longer load the back half of the compiler

The "structural, out of scope" reading above was too pessimistic. A shard does
need to BE a compiler, but only the parse lane of one; it loaded all ~665
modules because of three import edges, not because parsing needs them:

1. `driver_source_pipeline_parsing.spl` imported
   `driver_orchestration.{driver_streaming_surface_enabled}` and
   `driver_bootstrap.{bootstrap_entry_source_index}`. Both homes import the
   backends/MIR/LLVM/linker tier. The two predicates are now in the leaf
   `src/compiler/80.driver/driver_phase_gates.spl`; the old homes `pub use`
   them, so every caller is unchanged.
2. `driver_source_pipeline_loading.spl` carried
   `use lazy compiler.driver.watcher.watcher_client.{check_shb_freshness}` for a
   nested `check_shb_cache` helper with **zero callers**. `use lazy` is eager in
   the seed, and `watcher_client` imports `driver_api_compile_single` ->
   `driver.spl` -> everything. Deleted (dead code).
3. The shard entry itself was `native_build_worker.spl` -> `cli_native_build`,
   whose module evaluates `compiler.driver.driver` on load. New slim entry
   `src/app/cli/parse_shard_main.spl` -> `driver_parse_shard_entry.spl` builds
   the same CompileOptions the CLI builds and runs load_sources_impl +
   parse_all_committing_impl only. The `--entry-closure` walker moved verbatim
   from compile_targets.spl to `src/app/io/_CliCompile/native_build_closure.spl`
   so both entries share it. native_build_main.spl dispatches parse shards to
   the slim entry. HIR shards still use the full worker (they need
   lower_and_check_impl, which imports driver_bootstrap's MIR path).

Module-evaluation closure of the parse lane (call probe, seed interpret mode):

| lane | modules evaluated | RSS | wall |
|---|---|---|---|
| before (driver_source_pipeline_parsing) | 665 | 2.35 GB | 50 s |
| after edges 1+2 | 383 | 0.88 GB | 22 s |

Real shard 0 of 2 on the `lint_entry` closure (193 sources, cold cache), one
process, `/usr/bin/time -v`:

| entry | max RSS | wall |
|---|---|---|
| native_build_worker.spl (before) | 3.82 GB | 10 m 41 s |
| parse_shard_main.spl (after) | 1.54 GB | 9 m 58 s |

Remaining floor: `driver_types.spl` (CompileContext) imports `compiler.mir.*`,
`backend_port`, `codegen` and the three backend impls because the context
carries MIR/backend fields; that is the accepted floor for this change.

Pinned by `test/01_unit/compiler/driver/parse_shard_slim_entry_spec.spl`
(source-level, fast) and `scripts/check/check-parse-shard-rss-budget.shs`
(fail-closed RSS budget on a real shard, budget = 3x post-fix; pre-fix FAILs).

Both runs did identical work (`hits=0 misses=104 parses=104`); wall is the
parse itself. End-to-end `native-build --threads 2 --entry-closure` on a
3-file closure: the slim shards stored 3 entries and the HIR shard + main
worker read them back as `hits=3 misses=0 parses=0`. (That build then fails in
MIR on `std.text` — `unresolved method call: index_of/chars/merge` — identically
with `SIMPLE_PARSE_SHARDING=0`, so it is pre-existing and unrelated.)
