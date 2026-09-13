# AutoVectorize reverted to AnalysisOnly — four defects found hours after the flip

- **Status:** all four defects FIXED 2026-09-13. The pass stays AnalysisOnly:
  fixing the defects is not the same as proving the rewrite correct, and the
  remaining gate is an execution-level differential test (step 6 below).
- **Found:** 2026-09-13, adversarial review of the Active flip
- **Where:** `src/compiler/60.mir_opt/mir_opt/_AutoVectorize/rewrite.spl`,
  `auto_vectorize_codegen.spl`, `auto_vectorize_validate.spl`

`PassKind.AutoVectorize` was flipped to `Active` and reverted the same day. The
alias oracle (`auto_vectorize_alias.spl`, 15/15) and the runtime guard are
correct and stay. What is not correct is everything around them.

## D1 — the guard's span is computed from a hard-coded element width

`element_size_bytes(recipe.element_type)` decides `span_bytes`, and
`recipe.element_type` is a heuristic that is essentially always `"f32"`:
`recipe.spl:350` defaults to it, `:408` flips to `"i32"`, and
`auto_vectorize_validate.spl:243-246` `get_instruction_type` hard-codes
`Some("f32")` for every BinOp. So `span_bytes` is always `trip_count * 4`.

For an `f64` or `i64` loop that is **half the real span**. An overlap at
exactly `trip_count/2` elements then satisfies `diff >= span` and the loop is
vectorized with a write-before-read hazard — precisely the arrangement the
guard exists to reject. The guard is not conservative here; it is wrong.

## D2 — an unbounded guard falls through to the UNGUARDED rewrite

`rewrite.spl` computes `guard_usable = emit_guard and span_bytes > 0 and ...`,
and when it is false `entry_id` falls back to `new_header_id` — the blocks are
still spliced, the caller sees the block count change, and the rewrite is
applied with no guard at all. The commit message claimed the opposite ("worse
than not vectorizing"). Masked today only because D1 makes the width always 4.

## D3 — block ids collide on any real CFG

The splice assigns align = `header`, peel = `header+1`, vec = `header+2`, and
hard-codes the exit as `header+3`, while every original block with
`id > header` is pushed verbatim. A function shaped `bb0 -> bb1 (loop, exit ->
bb2) -> bb2` therefore ends with **two blocks with id 2**: the peel block
shadows the real exit (lookup is first-match), and the vector path exits to a
`bb4` that does not exist. Only `scalar_version` keeps the true exit edge.

The scheme predates this work, but the Active flip is what makes it fire on
real MIR for the first time. The single-block unit fixture exits to id 99 with
no continuation block, so it cannot observe the collision — which is why the
new block ids for the guard were deliberately taken above `max_block_id`,
while vec/peel were left on the old scheme.

## D4 — guard temporaries never enter `func.locals`

`create_alias_guard_block` numbers its temporaries from
`max_block_id * 4 + 1000` and never appends them to `func.locals`. The
convention elsewhere is `func.locals.len()` (`recipe.spl:127`), and
`core_codegen.spl:624-640` derives `unsigned_locals`/`ptr_locals` from
`body.locals` — so `diff`/`is_eq`/… have no type entry and can collide with
real locals in any function holding that many. Separately,
`Sub(Copy(out_base), Copy(in_base))` on GEP-base locals assumes a byte
difference; no lowering path for that was verified.

## Why revert rather than patch forward

Each of these is a wrong-answer-at-runtime risk, not a missed optimization, and
they compound: D1 makes the guard admit the hazard, D2 removes the guard
entirely in the case D1 hides, D3 corrupts the CFG for any function with a
continuation block, D4 corrupts locals. Shipping that combination is exactly
the silent miscompilation the oracle was built to prevent.

## To go Active again

1. Thread a real element type (or byte width) into the recipe, and make
   `get_instruction_type` return the operand's actual type rather than `"f32"`.
2. Make a non-usable guard **decline**, not fall through.
3. Move vec/peel/exit onto `max_block_id`-relative ids like the guard, and
   resolve the real exit block instead of assuming `header + 3`.
4. Append the guard temporaries to `func.locals` with types, and verify the
   pointer-difference lowering.
5. Re-add the witness contract — the identities are
   `auto_vectorize/exact-alias-elementwise-add` (positive) and
   `auto_vectorize/undecidable-distinct-bases` (negative), both previously
   executed through `run_auto_vectorize` and passing.
6. Add an execution-level differential test (the MIR interpreter exposes
   `execute_function`) comparing vectorized against scalar output, which is the
   check no structural test can substitute for.

## Fixed 2026-09-13

**D1 — real element width.** `get_instruction_type` no longer guesses; it
returns nil. `get_instruction_type_in(func, inst)` resolves the dest local's
declared type from `func.locals` via `mir_type_element_name`, which maps the
scalar MIR kinds and returns nil for anything else. nil means DECLINE, never a
default width. Pinned: f64/i64/f32 map correctly, Unit/Bool return nil, the old
`Some("f32")` guess is gone, and `element_size_bytes` gives 4 vs 8 for the
32/64-bit lanes whose distinction the guess erased.

**D2 — an unbounded guard declines.** `if emit_guard and not guard_usable:
return func`. It previously fell through and spliced the blocks with no guard
for a recipe the oracle had explicitly refused to clear. Pinned with a recipe
carrying an unmappable element type: block count must be unchanged.

**D3 — the exit block is resolved.** The header's real terminator is read out
of `func.blocks` and its non-self successor becomes the exit; a header naming
no block, or with no resolvable exit edge, declines instead of inventing
`header + 3`. Pinned with an orphan header id.

That fix also exposed a fixture bug of exactly the kind this record describes:
`make_elementwise_mul_recipe` claimed `header_block: 1` while
`make_elementwise_block_mul` IS block 2, so the mul rewrite had only ever
"worked" because the old code invented an exit. The fixture now names its own
block.

**D4 — guard temporaries are declared locals.** They are numbered from one past
the highest existing local id (the convention used elsewhere) and appended to
`func.locals` with an I64 type, instead of starting at an arbitrary constant
and never being declared. Pinned: the local count grows, and no id is
duplicated.

`auto_vectorize_spec.spl`: 88/88.

## Still required before Active

Step 6 of the list above, unchanged and unmet: an **execution-level
differential test** comparing vectorized output against scalar output. The MIR
interpreter exposes `execute_function`, so it is buildable. Every check in
place today is structural — it verifies the emitted blocks have the right
shape, not that running them produces the right numbers. That is the
substitution no amount of structural testing can make, and it is why the four
fixes here do not by themselves justify flipping the status.

## D5 — the emitted vector loop is UNLOWERABLE and UNEXECUTABLE

Found while building the execution-level differential test that step 6 asks
for. The test could not be built, and the reason is the most fundamental defect
in this record.

`create_vector_loop_block` emits its work as `MirInstKind.Intrinsic` addressed
by STRING NAME:

    simd_load_{element}x{width}
    simd_{op}_{element}x{width}
    simd_store_{element}x{width}

Nothing in the tree implements those names.

- `simd_lowering.spl` handles exactly **three**: `simd_add_f32x4`,
  `simd_mul_f32x4`, `simd_sub_f32x4`. No load. No store. No width other than
  f32x4.
- The MIR interpreter has no case for them either. Its unknown-intrinsic path
  is at least honest — `E-INTERP-INTRINSIC-Unknown` with a recorded
  `UnsupportedOperation`, not a silent 0 (Lane C8 fixed that) — so a vectorized
  function fails loudly rather than producing wrong numbers.

So for the 4-lane recipe the loop emits `simd_load_i32x4` and
`simd_store_i32x4`, which have no handler; and the AVX-512 planning level this
whole effort added emits `simd_load_f32x16` / `simd_add_f32x16` /
`simd_store_f32x16`, **none of which exist anywhere**.

The consequence is blunt: even with D1-D4 fixed and the alias oracle correct,
the code the rewriter produces cannot run. Flipping the pass Active would not
produce slow code or subtly wrong code — it would produce code that fails at
the first vector instruction.

This also explains why every defect in this record survived so long. The pass
has never been Active, the emitted intrinsics have never been executed, and the
unit fixtures only ever inspected block SHAPE. Four rounds of structural tests
all passed over a loop body that no backend can consume.

Pinned by three examples in `auto_vectorize_spec.spl`: `simd_load_*` and
`simd_store_*` are emitted; every emitted name for a 16-lane recipe lies
outside the three lowerable names; and load/store are emitted even for the
4-lane recipe.

### What step 6 now requires

The execution-level differential test is blocked behind implementing the
intrinsics, not merely writing the test:

1. implement `simd_load_*` / `simd_store_*` / `simd_<op>_*` in the MIR
   interpreter (the scalar oracle in `mir_simd_interpreter.spl` already models
   Vec16f/Vec8d/Vec16i lane semantics and is the obvious backing), **or**
   change the rewriter to emit `MirSimdLoad`/`MirSimdBinop`/`MirSimdStore`
   instructions that the interpreter already understands rather than
   string-named intrinsics;
2. extend `simd_lowering.spl` past the three f32x4 names it knows;
3. then, and only then, run vectorized against scalar and compare outputs.
