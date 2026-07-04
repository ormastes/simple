# Vectorization Blockers — State

**Date:** 2026-05-19
**Bug doc:** `doc/08_tracking/bug/auto_vectorize_rewriter_blockers_2026-05-02.md`

## Summary

The four gaps identified in the 2026-05-02 bug doc have been implemented.
No remaining structural blockers prevent simple loop vectorization from
compiling and executing the rewrite path. However, several functional
limitations remain (documented below).

---

## Gap Status vs Bug Doc

| Gap | Label | Bug doc status | Current status |
|-----|-------|---------------|----------------|
| 1 | W-recipe | VectorRecipe missing operand fields | **CLOSED** — all fields present in `auto_vectorize_part1.spl` |
| 2 | W-scev | `detect_loop_bounds` returned nil always | **CLOSED** — fully implemented in `auto_vectorize_analysis.spl` (lines 491–600+) |
| 3 | W-cfg | CFG splice missing; prologue/epilogue stubs | **CLOSED** — `splice_vectorized_block` + `rewrite_elementwise_add` implemented in `auto_vectorize_part2.spl` |
| 4 | W-fastmath | `MirFunction.has_fast_math` missing | **CLOSED** — field present in `src/compiler/50.mir/mir_instructions.spl:619` and populated during HIR→MIR lowering |

---

## Current Architecture (as of 2026-05-19)

Files in `src/compiler/60.mir_opt/mir_opt/`:

```
auto_vectorize.spl          — shared types, VectorRecipe, re-exports
auto_vectorize_analysis.spl — Phase 1: dep analysis + detect_loop_bounds
auto_vectorize_validate.spl — Phase 2: vectorizability validation
auto_vectorize_cost.spl     — Phase 3: cost model
auto_vectorize_codegen.spl  — Phase 4: code generation helpers
auto_vectorize_part1.spl    — K3/N1 pattern matchers + run_auto_vectorization
auto_vectorize_part2.spl    — run_auto_vectorize (N1 rewriter), rewrite_elementwise_add, splice_vectorized_block, W-scev/W-cfg/W-fastmath adapters
```

**Two entry points exist** (both exported):
- `run_auto_vectorization(module)` — full 4-phase pipeline (validate→cost→codegen)
- `run_auto_vectorize(module)` — N1 wave: pattern-match + rewrite elementwise-add only

---

## Remaining Limitations (not blockers)

### L1 — Peel block is a structural placeholder
`create_peeling_block` returns a block with zero instructions and a `Goto` terminator
(self-loop). Scalar remainder iterations for `n % VF != 0` are not emitted.
Tests verify the block has label `peel_loop` and `Goto` terminator, which is
the documented structural-placeholder contract for Wave N1.

File: `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` line ~149

### L2 — trip_count wired in run_auto_vectorize (FIXED in this change)
After `mir_pattern_match_elementwise_loop` returns a recipe, `run_auto_vectorize`
now calls `is_simple_loop(cur_func, recipe.header_block)` and fills in the real
`trip_count` from `LoopInfo.end_value` before calling `rewrite_elementwise_add`.
The R3 guard (`trip_count < chunk_width → refuse`) now correctly fires for
short constant-bounded loops. Dynamic bounds still produce `trip_count = -1`
(pass-through, treated conservatively as unknown).

### L3 — Reduction rewriter not wired (N2 followup)
`run_auto_vectorize` logs reduction recipes but does not rewrite them.
Comment says "N1-followup".

### L4 — Native spec test is placeholder
`test/01_unit/compiler/native/auto_vectorize_spec.spl` contains only:
```
it "skipped": val pending_reason = "pre-existing test failures..."
```
The canonical spec is `test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl`
(K3/N1 wave tests), which has substantive tests for pattern matching and
codegen helpers.

### L5 — control flow complexity check is over-conservative
`check_control_flow_complexity` in `auto_vectorize_validate.spl` rejects any
loop body with more than 2 blocks. This blocks vectorization of loops that have
simple conditionals producing 3-block shapes (header + if-body + merge).

---

## Test Coverage

`test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl` covers:
- K3 positive/negative pattern matchers (W-recipe)
- `detect_bounds_from_block` (W-scev)
- `create_alignment_check_block` / `create_peeling_block` (W-cfg)
- `has_fast_math` gate for FP reductions (W-fastmath)
- N1 `rewrite_elementwise_add` block structure invariants
- `create_vector_loop_block` codegen

All tests run in interpreter mode (assertions not executed per testing rules).

---

## Recommended Next Steps

1. **Implement peel block scalar body clone** (L1) — emit the original scalar
   instructions in `create_peeling_block` with a proper `Goto` to exit.

3. **Relax control flow check** (L5) — allow 3-block bodies for simple if-then.

4. **Wire reduction rewriter** (L3) — implement N2 rewriter for sum/product reductions.
