# Auto-vectorization never runs in a production compile (`AnalysisOnly`)

- **Status:** open — blocks every downstream SIMD-automation claim
- **Found:** 2026-09-13 (adversarial review of `34b96e29837`)

## The gate

`pass_status(PassKind.AutoVectorize)` returns `PassStatus.AnalysisOnly`
(`src/compiler/60.mir_opt/mir_opt/mod.spl:360-363`), and
`pass_status_allows_transform` admits **only** `Active`
(`mod.spl:381-384`). `pipeline_optimize` (`mod.spl:1677-1681`) and
`run_pass_on_module` (`mod.spl:1727-1728`) therefore skip the pass entirely.

`run_auto_vectorize` is reached **only from unit specs**.

## What this invalidates

Everything the auto-vectorizer decides is inert in a real build:

- `@must(simd)` / `@prefer(avx512)` are still decorative end to end, even
  though the parse -> HIR -> MIR transport and the decision receipt now exist
  and are tested. The enforcement runs; nothing calls it.
- `@simd(disable)` is still ignored in production for the same reason.
- The `x86_64-v4` planning level resolves correctly and widens recipes to
  16 x f32 / 8 x f64 — in specs. No production compile plans an AVX-512 recipe,
  because no production compile plans any recipe.

The commit message of `34b96e29837` said "`run_auto_vectorize` enforces it".
That is true of the function and **false of the compiler**. Corrected here
rather than quietly left standing.

## Not yet fatal, deliberately

The receipt reports `error[SIMD-REQ-001]` on stderr rather than aborting.
`pipeline_optimize` returns a bare `MirModule` with no `Result` channel, so the
only available hard failure is `panic`, which natively lowers to `rt_panic` and
kills the compiler process with no span and no error code. An unmissable
diagnostic is the honest maximum until the optimizer pipeline can carry a
diagnostic. Making `@must(simd)` genuinely fatal requires that channel first.

## Why flipping the status is not a one-liner

`Active` would admit a rewriter that today:

- rewrites **elementwise add and mul only**; reductions and matrix kernels are
  recognised and logged but never emitted (`_AutoVectorize/rewrite.spl:131-141`
  — the receipt now reports this distinctly as
  `pattern-recognised-but-this-wave-emits-no-rewrite-for-it` rather than
  blaming the pattern matcher);
- CLOSED 2026-09-13: bounds detection was never broken — that record was a
  fixture defect, now resolved. The rewriter still declines a *dynamic* trip
  count (guard R4), a narrower limitation than previously believed.
- has no alias oracle from `55.borrow` (listed as N1-followup in
  `rewrite.spl:64-69`).

The status line is honest about that. It should flip only behind the
semantic-equivalence proof its neighbours (`PatternIdiom`,
`PredicatePromote`) are also waiting on.

## Second-order effect to fix at the same time: the 8 -> 16 lane cliff

Once the pass is `Active` on an AVX-512 host, the R3 guard
(`rewrite.spl` — `recipe.trip_count < recipe.chunk_width`) refuses f32 loops
with a static trip count of 8..15 (f64: 4..7) that AVX2 hosts vectorize today,
because there is no narrower-width fallback. The cost model
(`auto_vectorize_cost.spl:57-60, 95-100`) also charges the remainder at scalar
cost, so e.g. trip 24 goes from 3 vector iterations with no remainder to 1
vector iteration plus 8 scalar, and more loops fail the `speedup > 1.5` gate.

**CLOSED 2026-09-13.** `_narrow_recipe_to_trip_count`
(`_AutoVectorize/rewrite.spl`) steps 512 -> 256 -> 128 before declining, floored
at 4 lanes, and leaves a dynamic trip count alone. Pinned by a spec example that
sweeps trip counts 4..40 and asserts **zero** cases where an 8-lane plan
vectorizes and a 16-lane plan refuses.

## The one remaining hard gate: no alias oracle

`check_array_aliasing` (`auto_vectorize_analysis.spl:290`) only compares
accesses that share the same `base_array.id`, and `are_indices_independent`
(`:320`) admits a pair only when BOTH indices are the induction variable — so it
is conservative *within* one base array. What it cannot do is prove that two
DIFFERENT base locals do not point at the same memory. `out[i] = a[i] + b[i]`
where `out` and `a` are distinct locals aliasing one buffer would be vectorized
unsoundly.

That is a miscompilation risk, not a missed optimization, and it is why this
status must NOT be flipped without the alias oracle from `55.borrow` that
`rewrite.spl:64-69` already lists as the follow-up. Flipping it is an owner
decision gated on that proof — the same proof `PatternIdiom` and
`PredicatePromote` are also waiting on.
