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
- cannot resolve a dynamic trip count — see
  `doc/08_tracking/bug/auto_vectorize_loop_bounds_detection_fails_2026-09-13.md`,
  which keeps every `for i in 0..n` loop out of reach;
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

A width ladder that retries 512 -> 256 -> 128 before declining is the fix, and
it must land with or before the status flip — otherwise `@must(simd)` on a
trip-12 loop passes on an AVX2 host and fails on an AVX-512 one.
