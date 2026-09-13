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

## D5 FIXED — the vector loop now emits executable SIMD MIR

Option (1) from the list above, taken: the rewriter no longer emits
string-named intrinsics at all. `create_vector_loop_block` now builds

    GetElementPtr   -> slice address
    MirSimdLoad(dest, addr, aligned, vec_type)
    MirSimdBinop(dest, lhs, rhs, "Add"|"Sub"|"Mul"|"Xor")
    MirSimdStore(value, addr, aligned)

which the MIR interpreter already executes (`mir_interpreter.spl:702-727`)
against the Vec4f/Vec8f/Vec16f, Vec4d/Vec8d, Vec4i/Vec8i/Vec16i lane model in
`mir_simd_interpreter.spl`.

`vector_mir_type(element, lanes)` maps to those types and returns nil for a
combination the interpreter does not model; `simd_binop_name(op)` maps the
recipe op to the interpreter's spelling and returns nil for anything else.
When either is nil the vector body is emitted EMPTY rather than filled with
instructions nothing implements — the failure stays visible to the caller
instead of being deferred to a backend that would reject the whole function.

Pinned by five examples: MirSimdLoad/Store/Binop are emitted and the
string-named Intrinsic count is **zero**; every supported width maps to a real
vector type; unsupported widths and elements decline; the op mapping covers
Add/Sub/Mul and declines div; and a 16-lane f32 recipe — the width the whole
AVX-512 planning effort produces, and the one that previously had no
implementation anywhere — emits a real vector body.

`auto_vectorize_spec.spl`: 93/93.

### Step 6 is now unblocked

The execution-level differential test no longer depends on implementing
anything: the emitted loop is executable by the MIR interpreter. What remains
is to build a fixture that is itself runnable — the current single-block
fixtures branch to a block that does not exist, so both the rewritten AND the
original fail and the control proves nothing — then run vectorized against
scalar and compare outputs.

`simd_lowering.spl` still knows only three f32x4 names, but that no longer
blocks the interpreter path; it matters for the native backend, and is tracked
separately.

## Step 6 DONE — and it found two more defects

The execution-level differential test now exists, runs, and passes. Writing it
was not the hard part; making the emitted function *execute* was, and the first
run did exactly what this record predicted no structural test could.

**D6 — the vector loop never advanced its induction variable.** The first
execution returned `InterpError::RuntimeError(Infinite loop detected)`.
`create_vector_loop_block` computed

    %vi1 = %vi + chunk_width          # a SEPARATE local
    %cond = %vi1 < trip_count
    If(%cond, vec_loop, exit)

and never wrote `%vi`. Every iteration re-entered with the same index, so the
back-edge was taken forever. `%vi` was also never initialised — no block seeded
it. Fixed: the increment writes back into `%vi` itself, the guard reads `%vi`,
and `align_check` (the only block dominating both the vector entry and the peel
fall-through) seeds `%vi = 0`. `%vi1` is deleted.

This is the defect that justifies the whole exercise. Four rounds of structural
tests, five D-numbered fixes, and a correct alias oracle all sat on top of a
loop that could not terminate — and nothing before this test could see it,
because block shape was perfect.

**D7 — a remainder trip count silently wrote one element.** With D6 fixed the
8-element case passed, so the sweep was widened to trip counts 4..17. Trip 9
failed with `undefined field 'instructions' ... on value of type 'nil'`. The
peel path is doubly wrong:

  * `create_peeling_block` emits exactly ONE cloned scalar iteration no matter
    how many remain, then leaves the loop — for trip 9 that writes `out[0]` and
    leaves elements 1..8 at their previous contents; and
  * it terminates at a hard-coded `header + 3`, a block that does not exist on
    any CFG with a real continuation. This is D3's assumption, removed from the
    vector path in the earlier round but left in the peel path.

The note in `rewrite.spl` claiming "Misaligned static trip counts are now
handled by create_peeling_block ... Defect C is resolved" was false.

Fixed by REFUSING it (`R4b`): `trip_count % chunk_width != 0` returns the
function unchanged. Refusing costs remainder loops an optimization; not
refusing miscompiles them. Lifting it requires a real peel that runs
`trip % chunk` iterations and exits to the resolved exit block, plus an
extension of the differential sweep to prove it.

R4b then made the width ladder refuse trip 12 under a 16-lane plan (it narrowed
to 8, and 12 % 8 != 0) — the exact "AVX-512 refuses what AVX2 accepts"
regression the ladder exists to prevent, arriving by a new route. The ladder
now narrows until the width both fits AND divides the trip count, so trip 12
lands on 4 lanes and is accepted.

### The tests

`auto_vectorize_spec.spl` is 98/98. The step-6 section holds five examples:

  * a scalar CONTROL that must run and produce the expected sums — without it
    a vector failure proves nothing;
  * byte-identical memory for the divisible case;
  * a sweep over trip counts 4..17 asserting scalar and vector agree;
  * a positive pin that trip counts 4/8/12/16 really are rewritten (block count
    grows), so the sweep cannot pass vacuously by declining everything; and
  * a negative pin that 5/6/7/9/10/11 are declined.

One existing spec asserted the OPPOSITE of D7 — "accepts misaligned trip count
(6 % 4 != 0) with peel body (Wave L3b)". What it pinned was the miscompile, so
it is inverted, with the execution evidence named in place.

## ACTIVE — 2026-09-13

`PassKind.AutoVectorize` is `PassStatus.Active` and the witness pair
(`auto_vectorize/exact-alias-elementwise-add` /
`auto_vectorize/undecidable-distinct-bases`) is re-added alongside it, since the
registry rejects an active pass with no witnesses just as it rejects an inactive
one that claims them.

**Admitted scope is deliberately narrow:** elementwise loops, static trip count
that is a whole number of lanes, cleared by the alias oracle or by the emitted
runtime range guard. Everything else declines. Widening means extending the
differential sweep first.

Measured consequence on the pass-registry specs, A/B on one tree with one
binary: baseline (AnalysisOnly) 11 failures across three specs, Active 13 — the
two new ones were the specs pinning the old status, now inverted.

The flip also fixed two PRE-EXISTING reds in `pass_status_spec.spl`, for a
reason worth recording: **AutoVectorize is the only Active pass in the entire
registry.** "invalidates shared facts conservatively after any admitted
transform" named `WriteCoalesce` as its transforming example, which is
analysis-only, so the assertion had no force and was red; "binds every retained
active transform to positive and negative witnesses" named `PatternIdiom`,
which is Disabled and therefore correctly advertises nothing, so it threw on
`unwrap`. Both rules needed an actually-active pass to point at and there was
none. `pass_status_spec.spl` is 12/12, including
`mir_pass_registry_integrity_errors()` and
`pass_witness_registry_integrity_errors()` both empty.

`simd_lowering.spl` still knows only three f32x4 names. That does not block the
interpreter path this record is about, but it means the NATIVE backend cannot
yet consume what the pass emits; tracked separately.

## D8 — the pass emitted AVX-512-shaped MIR that the AVX-512 selector REJECTED

Found immediately after the Active flip, by asking the question every earlier
check stopped one step short of: does the function this pass actually produces
reach real AVX-512 instruction selection?

It did not. Fed to `x86_plan_avx512_fixed` — the real admission
`isel_x86_64.spl:184` uses — the rewritten function came back:

    ok=false  reason=avx512-load-splat-gather-shape-mismatch  shapes=0
    simd_insts=4  locals=4

Four SIMD instructions emitted, **zero** vector locals declared, so zero shapes
planned and the whole function refused. On the native path the pass produced no
AVX-512 at all.

The cause is D4's fix applied to only half the problem.
`x86_plan_avx512_fixed` (`x86_64_avx512_isel.spl:53-59`) derives every vector
shape from `func.locals` declared types and from nothing else: inference
propagates only across copies and mask ops, and `MirSimdLoad` carries its vector
type but is **checked against** the shape rather than seeding it. D4 appended
the alias-guard temporaries to `func.locals`; the vector body's temporaries —
the two loaded slices, the result, the index, the exit flag and the three slice
addresses — were never declared at all.

Fixed with `vector_loop_locals(ctx, base_block_id)` in
`auto_vectorize_codegen.spl`, called at the splice next to the existing
guard-local append. The three vector values are declared with the real vector
MirType (`Vec16f` / `Vec16i` / `Vec8d`); the index, guard flag and addresses as
I64. It returns an empty list when the element/lane pair has no vector type,
matching the empty vector body emitted in that case.

After: `ok=true`, `reason=avx512-frame-values-planned`, `shapes=3`, `locals=12`,
for f32x16, i32x16 and f64x8 alike.

### Why nothing caught this

Every check in place stopped at the MIR. The pass emitted `MirSimdLoad` /
`MirSimdBinop` / `MirSimdStore` with correct vector types, the differential test
proved the INTERPRETER executed them and produced byte-identical results, and
the AVX-512 backend specs proved the selector admits well-formed vector MIR.
Each was true. The join was not, and nothing tested the join.

This is the same shape as D5 and D6 one level further out: D5 was "the emitted
instructions have no implementation", D6 was "the emitted loop does not
terminate", and D8 is "the emitted function is refused by the selector it was
built for". Each was invisible until something downstream was actually asked to
consume the output.

### The chain spec

`test/01_unit/compiler/mir_opt/auto_vectorize_avx512_chain_spec.spl`, 6/6. It
builds a plain scalar `out[i] = a[i] + b[i]` loop, runs the real rewrite, and
hands the result to the real admission — no hand-written vector MIR anywhere.

  * a control that the pass really did rewrite, so an admission verdict is not
    being read off an untransformed function;
  * admission for f32x16, i32x16 and f64x8, each asserting the exact success
    reason rather than just a boolean;
  * a direct pin that three vector-typed locals are declared, naming the cause
    rather than only the symptom; and
  * a negative control — a 4-lane recipe must NOT be admitted as AVX-512, so
    the positive examples say something about width.

### Correction to an earlier note

This record previously said `simd_lowering.spl` knowing only three `f32x4`
names was what blocked the native backend. That was wrong. `simd_lowering.spl`
is the legacy string-named-intrinsic lane and is not on this path at all: the
native x86_64 selector consumes `MirSimdLoad`/`MirSimdBinop`/`MirSimdStore`
directly (`isel_x86_64.spl:368-375`, `x86_64_avx512_isel.spl:91-135`). The real
blocker was D8, and it is fixed.

## What Active does and does not mean for the DB and web servers

Recorded because "AutoVectorize is Active" invites a reading it does not
support. The pass rewrites a loop only when ALL of these hold
(`rewrite.spl:307-374`):

  * the recipe kind is Elementwise and the op name contains "add" — sub, mul,
    div and everything else are matched and logged, not rewritten;
  * the trip count is a COMPILE-TIME CONSTANT. `is_simple_loop` sets
    `end_value` only for constant-bounded loops; a dynamic bound leaves
    `trip_count = -1` and R4 declines;
  * that constant is a whole number of lanes (R4b, see D7);
  * there are at least two input bases and an output base; and
  * the alias oracle clears the bases, or the emitted runtime range guard does.

Server code loops over runtime-length buffers — request bodies, row sets,
framebuffers sized at runtime. Those have no constant trip count, so **R4
declines them and the pass does nothing**. The honest answer to "are the DB
server and the web server automatically AVX-512 optimized by this pass" is
**no**, and no amount of the pass being Active changes that. What would change
it is a SCEV/runtime-trip-count path, which R4's comment already names as the
unblock condition.

### Where their AVX-512 actually comes from

Hand-written native kernels, dispatched by CPUID at runtime — not this pass:

  * DB: `rt_db_bitmap_and_u32` / `_or_` / `_andnot_u32`
    (`src/lib/nogc_sync_mut/db/accel.spl:180-223`);
  * scanning: `rt_simd_find_byte_span`, `rt_simd_bytes_equal_span`
    (`src/lib/common/simd_scan.spl:121-153`);
  * web/2D: `rt_engine2d_blend_const_span_pct_u32`,
    `rt_engine2d_blend_mask_span_u32`
    (`simple_web_html_layout_renderer_paint_primitives.spl`,
    `text_layout/font_rasterizer.spl`).

That those really are AVX-512 — rather than a `#[target_feature]` attribute LLVM
declined to act on — is checked by reading the binary, not by trusting the
attribute: `scripts/check/check-simd-kernels-vectorized.shs`, measured
`PASS — 9 kernel(s) checked, all vectorized`. That gate exists because three of
five kernels once carried the AVX-512 attribute and contained zero zmm
instructions, which no parity test can detect since a scalar kernel returns
identical answers.

## SUPERSEDED — runtime trip counts are now vectorized

The section above ("What Active does and does not mean for the DB and web
servers") concluded that the answer for server code is **no**, because R4
refused any loop whose length is not a compile-time constant. That conclusion
was correct about the code as it stood and wrong as a place to stop: the
refusal was a limitation to remove, not a fact to document. It has been
removed.

### What changed

**The loop bound is an OPERAND, not a number.** `_loop_bound` reads the
header's `i < n` test and returns both halves — the bound operand and the local
being compared. `Copy(n_local)` is as usable as `Const(1024)`, so a request
body, a row set or a framebuffer sized at runtime vectorizes exactly like a
fixed-length array.

**The guard asks whether a whole vector fits**, not whether iterations remain:
`%lim = bound - VF; %cond = %i <= %lim`. An `%i < n` test would enter the body
with fewer than VF elements left and read past the end of all three arrays.

**The remainder is the scalar loop itself.** The vector loop indexes on the
loop's own induction variable and, when fewer than VF elements remain, branches
into an unmodified clone of the scalar body — which re-tests its own `i < n`
and finishes from exactly where the vector loop stopped. The old "peel" block
is deleted. That one change also retires R4b (D7): a remainder is no longer a
special case that had to be refused, it is just the scalar loop doing its job.

The scalar clone was already being built as the alias-guard fallback. It now
serves both roles, so there is one copy of the scalar semantics instead of the
peel block's separate and wrong one.

### Two defects found while doing it

**Block-id collision.** The splice occupies `header+0` (align_check) and
`header+2` (vec_loop), while the clone took `max_block_id+2`. On a
single-block function `header == max_block_id`, so the clone landed on the
vector loop's own id and first-match lookup silently resolved to whichever came
first. New ids now clear both the existing blocks and the splice's own.

**The index local was the wrong one.** The pattern matcher reports the
increment's DEST as the induction variable — `%5` for `%5 = %4 + 1` — while the
loop compares the pre-increment name `%4`. Indexing on the recipe's answer
found no comparison and declined every loop the driver offered. The candidate
set now follows the `+ const` edge backwards, and the vector loop indexes on
whichever local the bound actually tests. The symptom was sharp: the
end-to-end driver examples went red while the direct-rewrite ones stayed green,
because their fixture happens to increment the compared local in place.

### Evidence

`auto_vectorize_spec.spl` 101/101, `auto_vectorize_avx512_chain_spec.spl` 7/7.

The load-bearing examples are executions, not shapes:

  * a scalar control with the bound in a local, which must run and be right
    before any vector claim means anything;
  * the rewrite fires with `trip_count = -1` — previously an unconditional
    decline; and
  * **identical memory for every runtime length 1..20**, including lengths
    shorter than a single vector, where the preheader guard must send control
    straight to the scalar loop without reading anything.

And the chain closes for the runtime case: a dynamic-bound loop fed to
`x86_plan_avx512_fixed` returns `ok=true, avx512-frame-values-planned`. A loop
whose length the compiler does not know now reaches real AVX-512 selection.

Four specs that pinned the old refusals are inverted, each naming why. The
too-short refusal (trip 3 with VF 4) is unchanged and still declines — that one
is a genuine "not worth a vector", not a limitation.

### Still true from the superseded section

The op must still be elementwise **add**, and the alias oracle must still clear
the bases or the runtime range guard must cover them. The hand-written kernels
listed there remain the source of the DB and web servers' AVX-512 today; what
has changed is that the pass is no longer structurally incapable of helping
them.
