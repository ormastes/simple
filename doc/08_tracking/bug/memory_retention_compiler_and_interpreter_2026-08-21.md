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
