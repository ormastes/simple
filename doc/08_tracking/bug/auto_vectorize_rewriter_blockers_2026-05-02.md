# Bug: Auto-Vectorize MIR Rewriter — Prerequisite Analysis Infrastructure Missing

**Date:** 2026-05-02
**Wave:** L3 (MIR rewriter)
**Status:** BLOCKED — stop condition met; no rewrite code written
**Filed by:** L3 agent (Wave L)

## Summary

Wave L3 was tasked with implementing the MIR rewriter in
`src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` for the two patterns
recognised by Wave K3 (elementwise add/mul and reduction sum). After reading
all mandatory reference files and verifying the MIR op inventory, four
blocking gaps were identified. The MIR SIMD ops themselves are **not** the
blocker (they exist; see §5). The blocker is the analysis infrastructure that
any sound rewriter requires.

## Stop-condition triggered

> "The MIR rewriter would need a borrow-analysis pass / upstream analysis that
> doesn't exist — file a bug doc + leave the pattern matcher in place + exit."

All four gaps below must be resolved (in separate prerequisite waves) before
Wave L3 can emit a semantics-preserving rewrite.

---

## Gap 1 — VectorRecipe operand fields missing (W-recipe)

**File:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl`

`VectorRecipe` (K3) stores only instruction **counts** and the induction-var
`LocalId`. It does not carry:

- `input_bases: [LocalId]` — the `LocalId`s of the GEP base arrays for
  input operands (`a`, `b` in the elementwise case).
- `output_base: LocalId?` — the GEP base for the store destination.
- `accumulator: LocalId?` — the scalar accumulator register for the
  reduction case.
- `induction_update: LocalId` — the `dest` of the `BinOp(Add, %i, 1)`
  instruction (K3 stores this as `induction_var` but it is the *updated*
  value, not the pre-increment variable; the rewriter needs both to build
  the `+VF` induction step).

Without these fields, the rewriter cannot construct `MirSimdLoad(ptr_for_a)`
or `MirSimdStore(ptr_for_out)` — it does not know which locals to pass as
base pointers.

**Fix required (W-recipe):** Extend `VectorRecipe` and both pattern matchers
to extract and record GEP base operands for every Load/Store in the body
block. The GEP-info machinery already exists in
`auto_vectorize_analysis.spl::collect_array_accesses`; the matchers just need
to call it and stash the results.

---

## Gap 2 — LoopInfo population returns nil; no trip-count extraction (W-scev)

**File:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl`

`detect_loop_bounds` (called by `is_simple_loop`) explicitly returns `nil`:

```
fn detect_loop_bounds(...) -> LoopInfo?:
    """...Simplified: looks for pattern like: i < N"""
    # This would require more complex pattern matching
    # For now, return a simple default loop
    # Real implementation would analyze phi nodes and comparison operations
    nil
```

`VectorRecipe.trip_count` is always `-1` (hardcoded in both K3 matchers).

The task spec requires:
- trip count < 4 → scalar (no rewrite)
- trip count ≥ 4 → vectorize

Without a real trip count, the rewriter has two choices, both wrong:

1. Always vectorize: generates out-of-bounds SIMD loads when `n % VF != 0`
   and `n < VF`. Breaks scalar semantics.
2. Never vectorize: the pass becomes a no-op (same as K3 skeleton).

**Fix required (W-scev):** Implement `detect_loop_bounds` to parse the loop
condition (`CmpLt(%i, %n)`) and extract `%n` as the trip-count bound.
Even a conservative constant-only extractor (return nil for non-constant
bounds) would unblock the rewriter for the unit-test fixtures which use
concrete bounds.

---

## Gap 3 — CFG splice primitive missing; prologue/epilogue are empty stubs (W-cfg)

**File:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl`

Both CFG-manipulation helpers are explicitly marked placeholder:

```
fn create_alignment_check_block(...) -> MirBlock:
    # Simplified: just create a placeholder block
    ...

fn create_peeling_block(...) -> MirBlock:
    # Peeling loop: runs until alignment is achieved
    # Simplified: placeholder
    ...
```

`generate_epilogue` clones scalar body blocks with `id + 1000` offset but
never re-wires the header terminator (`If %i_ge_n → BB_body, BB_exit`) to
branch to the new vector-body header or the epilogue header. There is no
`splice_vector_loop_with_tail(func, orig_header, vectorized) -> MirFunction`
primitive that correctly replaces the original loop in the function's block
list with `[vector_header, vector_body, epilogue_header, epilogue_body]` and
fixes all `Jump`/`If` targets.

Without this, any emitted SIMD instructions would sit in detached blocks that
are never reached.

**Fix required (W-cfg):** Implement a `splice_vector_loop_with_tail` function
that:
1. Given the original loop header `BlockId` and a `VectorizedLoop` struct,
   replaces the header's `If` exit edge to point to the vector body.
2. Wires the vector body's back-edge to the vector header (step `+VF`).
3. Adds the scalar epilogue as a separate block chain entered when
   `i + VF > n` (the tail guard).
4. Preserves `BB_exit` as the final successor of the epilogue tail.

---

## Gap 4 — MirFunction carries no has_fast_math flag; FP reductions must be refused (W-fastmath)

**File:** `src/compiler/50.mir/mir_data.spl` (or equivalent MirFunction
definition)

`MirFunction` has no `has_fast_math: bool` field. Design doc §10 states:

> "FP reductions require explicit fast-math permission (§8 failure mode);
> the rewriter MUST default to refusing FP reductions."

The K3 reduction matcher hardcodes `element_type = "f32"` for every recipe:

```
Some(VectorRecipe(
    ...
    element_type:  "f32",
    ...
))
```

Therefore **every** reduction recipe that K3 emits is a floating-point
reduction. Without `has_fast_math`, the Wave L3 rewriter must refuse all
of them (0% of current reduction recipes are rewritable). This does not
block the elementwise rewriter (which is integer-safe), but it means the
reduction pattern produces no MIR output in Wave L3.

**Fix required (W-fastmath):** Add `has_fast_math: bool` to `MirFunction`
(default `false`). Thread the annotation from function-level `@fast_math`
pragmas (or equivalent Simple syntax) through the HIR→MIR lowering pass.
Update the reduction matcher to propagate the flag into `VectorRecipe` as
a `has_fast_math: bool` field.

Additionally, the reduction matcher should detect integer element types
(`i32`, `i64`) from Load destination types rather than hardcoding `"f32"`,
so that integer reductions (which are always safe to reorder) can be emitted
without the fast-math gate.

---

## Gap 5 — NOT a blocker: MIR SIMD ops confirmed present

For clarity, the following ops exist in
`src/compiler/50.mir/mir_instructions.spl` and are available to a future
rewriter **without any new compiler layer work**:

| Op | Signature |
|----|-----------|
| `MirSimdLoad` | `(dest: LocalId, ptr: MirOperand, aligned: bool, vec_type: MirType)` |
| `MirSimdStore` | `(val: MirOperand, ptr: MirOperand, aligned: bool)` |
| `MirSimdBinop` | `(dest: LocalId, lhs: MirOperand, rhs: MirOperand, op: text)` |
| `MirSimdReduce` | `(dest: LocalId, src: MirOperand, op: text)` |
| `SimdAddF32x4` | `(dest: LocalId, a: MirOperand, b: MirOperand)` |
| `SimdAddI32x4` | `(dest: LocalId, a: MirOperand, b: MirOperand)` |
| `SimdAddI32x8` | `(dest: LocalId, a: MirOperand, b: MirOperand)` |
| `SimdHaddF32x4`| `(dest: LocalId, a: MirOperand)` (horizontal add) |

The `mod.spl` dispatch arm for `"auto_vectorize"` is also already wired
(line 463).

---

## Recommended follow-up wave sequencing

```
W-recipe   — Extend VectorRecipe fields (1 file, auto_vectorize.spl)
W-scev     — Implement detect_loop_bounds (1 file, auto_vectorize_analysis.spl)
W-fastmath — Add has_fast_math to MirFunction (2 files: mir_data.spl + matchers)
W-cfg      — Implement splice_vector_loop_with_tail (1 file, auto_vectorize_codegen.spl)
Wave L3b   — Wire rewriter once all 4 prerequisites land
```

W-recipe and W-scev are independent and can run in parallel. W-cfg depends on
W-recipe (needs the full recipe). W-fastmath is independent. Wave L3b depends
on all four.

---

## Files examined

- `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` — K3 skeleton (unchanged)
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_types.spl` — LoopInfo struct
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl` — detect_loop_bounds (nil)
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` — placeholder codegen
- `src/compiler/60.mir_opt/mir_opt/mod.spl` — dispatch arm (already wired)
- `src/compiler/50.mir/mir_instructions.spl` — MirInstKind enum (SIMD ops present)
- `doc/05_design/simd_auto_vectorize_design.md` — §10 phased rollout
- `test/unit/compiler/mir_opt/auto_vectorize_spec.spl` — K3 tests (not touched)
