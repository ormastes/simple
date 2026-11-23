# JIT startup: serial Cranelift codegen made tab-bar slower under the JIT than the interpreter

**Status:** PARTIAL. Codegen and liveness now run off the critical path. On
tab-bar 1x the JIT reaches parity with the interpreter (~3.0 s each) but is not
clearly faster. The remaining critical path is serial MIR→CLIF translation; see
"Next".
**Found:** 2026-11-24. This follows
`jit_block_entry_sync_all_vars_quadratic_compile_2026-11-23.md`.
**Regression spec:** `src/compiler_rust/compiler/tests/jit_parallel_codegen.rs`.

## Symptom

After the 2026-11-23 live-in sync fix, tab-bar 1x took ~5.4 s under the JIT
and ~3.0 s under the interpreter (after #11113 cut engine acquire). Reachability
pruning leaves ~4,300 functions. Each one went through translate, verify and
`Context::compile` on one thread.

## Fixes

1. **Codegen on workers.**
   - `function_alignment.rs`: `define_function_aligned` is split into
     `compile_aligned(isa, ctx)` and `define_compiled(...)`. AOT callers are
     unchanged.
   - `common_backend.rs`: `compile_function` is now `translate_function`, then
     `codegen_translated` (verify + compile), then `define_translated`.
   - `compile_bodies_parallel` translates on the calling thread, which owns
     `&mut module`. It sends each `Context` to the least-loaded worker over
     that worker's own channel, so there is no shared queue and no lock.
   - Results are defined back in submission order through a reorder buffer, so
     the define sequence and code layout match the serial loop.
   - A worker panic is resumed at its define point. Failures are reported in
     function order.
   - The JIT sets `codegen_workers` from `SIMPLE_JIT_CODEGEN_THREADS`, or
     `min(4, cores)` when unset. A value of 0 or 1 means serial. Modules under
     64 functions stay serial, and AOT/object backends never enable it.
2. **1,024-context window.** A window of `workers * 4` stalled translation
   behind bursts of large functions: the main thread waited 190 ms in recv on
   tab-bar. The wide window costs ~50 MB RSS (2.07 → 2.11 GB).
3. **Outlining liveness is lazy.** `expand_with_outlined` computed
   `compute_live_ins` for every function, but only functions that own an
   outlined body need it. Expand went from ~200 ms to ~50 ms.
4. **Liveness on a helper thread.** `compute_live_ins` cost ~150 ms of the
   serial translate path. A scoped producer thread now computes it one function
   ahead, in loop order (`sync_channel(256)`), and hands it to
   `compile_function_body(..., live_ins: Some(..))`. The serial path passes
   `None`.

## Evidence

- Red/green, `jit_parallel_codegen`: base ratio **1.00**, fixed **0.41–0.49**.
  The run is 120 functions × 40 if-expressions, best of 3, alternating, and
  values are checked against a closed form. The assertion is skipped on fewer
  than 4 cores.
- Tab-bar main-thread breakdown with 4 workers, before fix 4:
  - translate 876 ms (setup 201, of which liveness 149 and vreg types 38;
    block loop 412; sealing 202);
  - waits 192 → ~10 ms after the window change;
  - define 15 ms.
  - Worker codegen totals 2.6 s of CPU.
- With fix 4, the body loop is ~820 ms with 4 workers. 6 and 8 workers change
  it by ≤ 40 ms, which is noise.
- The A/B table and identity matrix are in the wiki section dated
  2026-11-24 "JIT startup 2".

## Remaining tab-bar budget (~3.0 s)

| phase | ms |
|---|---|
| load + parse with imports | 360 |
| HIR lowering (Pass 0.5b import type loads ~370, bodies ~330) | 820 |
| MIR lowering (function bodies 290, of which unreachable 89; setup ~200) | 490 |
| reachability, extern scan, JIT init | ~150 |
| expand / dedupe / inline / declare | ~120 |
| body loop (serial translate-bound) | ~820 |
| finalize, module init, render, teardown | ~250 |

**Measured and rejected:**
- Pruning before MIR lowering saves at most 89 ms, and it changes counter
  ordering and error behaviour.
- Freeing AST/HIR/MIR on a background thread at exit gave no measurable change.
- More codegen workers do not help, because translation is the bottleneck.

## Next (design, not done here)

- **Seal blocks early.** Sealing every block at the end costs ~200 ms of
  translation. A block can be sealed once all of its MIR predecessors'
  terminators are emitted. This is only safe if no lowering helper adds an edge
  into a MIR block outside the terminator, for example the generator and async
  dispatch blocks. That must be proven first, because release Cranelift does not
  check sealed-block predecessors.
- **Parallel translation.** `compile_function_body` needs `&mut module` for
  `declare_func_in_func`/`declare_data_in_func` and on-demand declarations, and
  `&mut func_ids`. Pre-declaring every callee and data object before the loop
  would let translation run per worker on a read-only view.
- **HIR Pass 0.5b** (`load_imported_types`, ~370 ms) is memoized per
  `(unit, import target)`. That key re-walks one module once per symbol group.

## HIR import type loads — probe, 2026-11-24 (no change made)

Measured on tab-bar with the JIT, using a probe build that was not committed.

- `load_imported_types`:
  - 2,817 calls: 1,985 cache hits and 832 misses.
  - The misses cover 369 units; 148 of those units are loaded under more than
    one symbol group.
  - Most repeated: `io_runtime.spl` ×30, `simple_web_html_layout_renderer_foundation.spl` ×20,
    `draw_ir.spl` ×16, `engine2d/backend.spl` ×15, `sfnt.spl` ×14.
- `register_imported_symbols_from_items`: 302 ms in total. These timers are
  inclusive, because `load_reexported_symbols_from_items` recurses.
  - Pass 0: ~0 ms.
  - Pass 1: 10 ms.
  - Pass 2 (transitive): 36 ms.
  - Tail: 251 ms. This is re-exports, which recurse into nested loads, plus
    the trait capture and `materialize_import_aliases`.
- **Next step:** profile the tail exclusively, nested loads excluded, before
  choosing a cache. A per-unit cache (instead of per `(unit, target)`) would
  remove up to 463 repeated loads. The per-target filter in Pass 1 and in the
  alias materialization is load-bearing for type correctness (see the comments
  in `load_imported_types`), so it needs a union-of-targets design, not a plain
  key change.
