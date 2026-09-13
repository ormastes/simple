# AutoVectorize reverted to AnalysisOnly — four defects found hours after the flip

- **Status:** open — Active is the correct destination; these gate it
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
