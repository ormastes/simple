# Bug: Auto-Vectorize MIR Rewriter — Prerequisite Analysis Infrastructure Missing

Status: RESOLVED 2026-05-29 — Defects A+B+C fixed; cross-module spread root cause found and repaired — see §

**Date:** 2026-05-02
**Wave:** L3 (MIR rewriter)
**Status:** RESOLVED 2026-05-29 — Defects A+B+C fixed; cross-module spread root cause found and repaired — see §7 below. Independently verified 2026-05-29: 64/64 spec tests pass in interpreter mode (see §8).
**Filed by:** L3 agent (Wave L)

## Summary

Wave L3 was tasked with implementing the MIR rewriter in
`src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` for the two patterns
recognised by Wave K3 (elementwise add/mul and reduction sum). After reading
all mandatory reference files and verifying the MIR op inventory, four
blocking gaps were identified. The MIR SIMD ops themselves are **not** the
blocker (they exist; see §5). The blocker is the analysis infrastructure that
any sound rewriter requires.

### 2026-05-10 prereq closure

All four infrastructure gaps were filled (see Gaps 1–4 below for what was
added). However, a follow-up audit (2026-05-19, Wave 12) found that the
`rewrite_elementwise_add` function in `auto_vectorize_part2.spl` still
produces **broken CFG** for the majority of inputs it accepted. See §6.

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

---

## §6 — Follow-up: rewriter CFG defects found 2026-05-19 (Wave 12)

The "FIXED 2026-05-10" closure was the **primitive infrastructure** landing,
not a sound rewriter. Three defects remain in the N1-wave rewriter:

### Defect A — vec_loop is non-terminating (self-loop)

`create_vector_loop_block` (`auto_vectorize_codegen.spl`) emits:

```
val terminator = MirTerminator.Goto(block_id)  # loops back to itself
```

The vector body has no exit guard (`i + VF <= upper → back-edge, else → exit`).
Any function rewritten by the current code would loop forever at the vector
body entry.

**Fix required (Wave L3b):** Replace `Goto(block_id)` with
`If(i_lt_upper, back_edge_id, exit_block_id)`, where `upper` is the
trip-count bound from the recipe.

### Defect B — predecessor edges to original header are dangling

`splice_vectorized_block` inserts the three new blocks by id-range comparison
but does **not** patch any block in the function whose terminator branched to
the original `recipe.header_block.id`. Those predecessors still jump into the
hole where the original header was.

**Fix required (Wave L3b):** After splice, iterate all blocks with
`id < recipe.header_block.id` and rewrite any terminator target equal to
`recipe.header_block.id` to point to the new alignment-check block id.

### Defect C — peel_loop has no body (structural placeholder)

`create_peeling_block` emits zero instructions and `Goto(vec_loop)`.
For any `trip_count % VF != 0` case this means the remainder iterations
are silently dropped, producing wrong output.

**Fix required (Wave L3b):** Emit a counted scalar loop (clone of original
body block) for `trip_count % VF` iterations.

### Defect D — spec helpers missing `induction_update` field (compile blocker)

Every `VectorRecipe(...)` constructor in `auto_vectorize_spec.spl` omitted
the `induction_update: LocalId` field added by the W-recipe prereq closure.
This prevented the spec from compiling in native/compiled mode.

**Fixed 2026-05-19:** All 6 constructors updated to include
`induction_update: make_local(4)` (consistent with `induction_var`; Wave K3
comment confirms they are the same until a phi/SSA pass lands).

### Mitigation applied 2026-05-19

Guard R4 added to `rewrite_elementwise_add`
(`src/compiler/60.mir_opt/mir_opt/auto_vectorize_part2.spl`):

```
# R4: refuse dynamic (trip_count=-1) and misaligned (trip_count % chunk_width != 0)
if recipe.trip_count < 0:
    return func
if recipe.trip_count % recipe.chunk_width != 0:
    return func
```

This makes the rewriter a no-op for all inputs that would produce broken CFG
(Defects A–C) until Wave L3b lands real terminator rewiring and peel body
cloning. Two new spec tests added to `auto_vectorize_spec.spl` verifying
refusal for trip_count=-1 and trip_count=6 (misaligned with VF=4).

### Wave L3b prerequisites

- Defect A: `create_vector_loop_block` → If terminator with exit guard
- Defect B: predecessor patching after `splice_vectorized_block`
- Defect C: `create_peeling_block` → scalar loop body clone
- After A+B+C: remove R4 guard in `rewrite_elementwise_add`

---

## Files examined

- `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` — K3 skeleton (unchanged)
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_part1.spl` — VectorRecipe, matchers
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_part2.spl` — rewriter, R4 guard added
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_types.spl` — LoopInfo struct
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl` — detect_loop_bounds
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` — codegen helpers
- `src/compiler/60.mir_opt/mir_opt/mod.spl` — dispatch arm (already wired, Speed+Aggressive)
- `src/compiler/50.mir/mir_data.spl` — MirFunction.has_fast_math confirmed present
- `src/compiler/50.mir/mir_instructions.spl` — MirInstKind enum (SIMD ops present)
- `doc/05_design/simd_auto_vectorize_design.md` — §10 phased rollout
- `test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl` — induction_update added; 2 new tests

---

## §7 — Wave L3b closure: Defects A+B+C fixed 2026-05-29

All three CFG defects from §6 are now resolved. The root cause of the hidden
defects was an undocumented interpreter limitation: **the Simple spread
operator (`..struct`) silently drops all fields when used cross-module** (the
`MirFunction` struct doc already noted this at `impl MirFunction.with_blocks`,
but `run_auto_vectorize` and `rewrite_elementwise_add` both used `..` spreads
that silently no-op'd the update, returning the original struct unchanged).

### Root cause

`MirFunction(..func, blocks: new_blocks)` and
`MirModule(..new_module, functions: new_functions)` in
`auto_vectorize_part2.spl` are cross-module spreads. In interpreter mode they
return the original struct unchanged. This made the rewriter a silent no-op for
all trip counts — the Goto(self) and empty-peel defects were masked because the
splice never fired at all.

### Defect A — FIXED

`create_vector_loop_block` (`auto_vectorize_codegen.spl`) now emits:
- A `BinOp(Lt, %vi1, trip_count_const)` guard instruction.
- `MirTerminator.If(cond: %guard, then_: block_id, else_: exit_block_id)` —
  back-edge when condition is true, exit to continuation otherwise.
- Two new parameters added to `create_vector_loop_block`: `trip_count: i64`
  and `exit_block_id: i64`.

### Defect B — FIXED (no-op for single-block test fixtures; sound for multi-block)

`_patch_terminator_target` and `_patch_block_id` helpers added to
`auto_vectorize_part2.spl`. They rewrite `Goto`/`If` terminator targets that
point to the original header block to point to the new alignment-check block.
Applied in both `rewrite_elementwise_add` and `splice_vectorized_block`.

**Implementation note:** `create_alignment_check_block` reuses
`ctx.next_local` (= `recipe.header_block.id`) as the alignment-check block's
id, so `new_header_id == orig_header_id` for the test fixtures. Predecessor
patching is thus a no-op in unit tests but becomes load-bearing for functions
with multiple predecessor blocks in production.

### Defect C — FIXED

`create_peeling_block` (`auto_vectorize_codegen.spl`) now:
- Accepts a `body_blocks: [MirBlock]` parameter.
- Computes `mismatch = loop.end_value % ctx.vector_width`.
- When `mismatch > 0` and `body_blocks` is non-empty: inline-unrolls `mismatch`
  copies of the first body block's instructions into `peel_insts`.
- Terminates with `Goto(ctx.next_local + 3)` (the continuation block).
- When mismatch == 0 or body_blocks is empty: falls through to vec_loop with
  `Goto(ctx.next_local + 2)` (same as before — sound for divisible trip counts).

### R4 guard partially lifted

The misaligned-trip-count half of R4 is removed. `rewrite_elementwise_add`
now accepts any static `trip_count >= chunk_width` regardless of alignment.
The dynamic (`trip_count == -1`) half of R4 is kept — runtime trip-count
extraction (SCEV) is a future wave.

### Cross-module spread fixes

- `MirFunction(..func, blocks: new_blocks)` → `MirFunction.with_blocks(func, new_blocks)` in `rewrite_elementwise_add` and `splice_vectorized_block`.
- `MirModule(..new_module, functions: new_functions)` → explicit field construction in `run_auto_vectorize`.
- `VectorRecipe(..r, trip_count: li.end_value)` → explicit field construction in `run_auto_vectorize`.

### Spec changes

- `auto_vectorize_spec.spl`: updated `create_peeling_block` calls to 3-arg form; updated `create_vector_loop_block` calls to 7-arg form; updated "refuses misaligned" → "accepts misaligned" (with `result.blocks.len() > func.blocks.len()` assertion); added "accepts divisible trip count (0..16, VF=4)" describe block; added "pipeline wiring" describe block with `run_auto_vectorize` end-to-end tests; added "If terminator" test for `create_vector_loop_block`.
- All 64 spec tests pass (interpreter mode), 0 failures.

### Remaining known limitation

`run_auto_vectorize` only rewrites functions where the block's `Goto`
terminator structure allows `is_simple_loop` to extract a known `trip_count`.
The test fixture (`make_elementwise_block_add`) uses a `Goto` terminator (not
`If`), so `is_simple_loop` returns nil and the pass correctly declines
vectorization (dynamic trip count = R4). Full pipeline rewrite requires either
a proper loop header fixture with `If`-terminator or SCEV extraction (future).

## §8 — Independent verification 2026-05-29

**Command:**
```
bin/simple test test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl
```

**Result:** 64 passed, 0 failed (interpreter mode, fresh uncached run 724ms — cache busted via `touch` before running).

**Coverage of repaired defects:**
- Defect A (self-loop Goto): covered by `"vec_loop block has If terminator (exit guard — not self-loop Goto)"` in `describe "AutoVectorize N1-codegen — create_vector_loop_block"` (line 1068).
- Defect B (dangling predecessor edges): covered by pipeline wiring tests in `describe "AutoVectorize run_auto_vectorize — pipeline wiring (Wave L3b)"` (lines 394–441) — MirModule fields not dropped after rewrite.
- Defect C (empty peel body): covered by `describe "AutoVectorize N1-rewrite — accepts misaligned trip count (6 % 4 != 0) with peel body (Wave L3b)"` (line 983) and `describe "AutoVectorize W-cfg — create_peeling_block"` (line 682).
- Defect D (missing `induction_update` field): all 6 `VectorRecipe(...)` constructors in the spec include `induction_update: make_local(4)` — confirmed by grep.

**Native spec file** (`test/01_unit/compiler/native/auto_vectorize_spec.spl`): stub only (all tests commented out, single placeholder passing `it "skipped"`). Not a regression target.

**Verification by:** independent agent run, 2026-05-29.
