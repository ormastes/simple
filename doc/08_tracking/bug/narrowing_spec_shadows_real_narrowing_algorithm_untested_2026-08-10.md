# narrowing_spec.spl shadows NarrowingContext/Fact/Scope — real narrowing algorithm untested

- **File**: `test/unit/compiler/semantics/narrowing_spec.spl:1-60`
- **Real product code**: `src/compiler/35.semantics/narrowing.spl`
- **Found during**: bounded first pass on `spec_shadow_reimplementation_worklist.tsv`
  (spec-vacuity SHADOW family, `doc/08_tracking/test/spec_vacuity_families_full_corpus_census.md`)

## What's wrong

The spec declares local copies of `NarrowingFact`, `NarrowingScope`, and
`NarrowingContext` (header comment: "All types defined locally for interpreter
mode compatibility... mirror src/compiler/35.semantics/narrowing.spl") instead
of importing the real types. Confirmed real divergence, not just a naming
coincidence:

- Real enum is `NarrowingCondition` (`narrowing.spl:24`); the spec's local
  enum is named `NarrowingConditionKind` — a different name, so the census's
  exact-name-match filter didn't even flag it, but it's the same shadow
  pattern.
- Real `NarrowingContext.lookup()` returns `HirType?` (`narrowing.spl:87`);
  the spec's local `lookup()` returns `text?` — a simplified stand-in.
- The real module's actual narrowing *algorithm* — `analyze_condition`,
  `_analyze_binary_condition`, `_analyze_is`, `_analyze_exists_check`,
  `_analyze_truthiness`, `negate_facts`, `_combine_facts` — all operate on
  `HirExpr`/`HirType` and are **never exercised by this spec at all**. The
  spec only tests scope push/pop/lookup bookkeeping on its own simplified
  clone, not the real condition-analysis logic that is the actual point of
  the module.

## Why not fixed in this pass

Fixing properly means building `HirExpr`/`HirType` fixtures to drive
`analyze_condition` and friends against the real HIR-typed API — a real test
rewrite, not a bounded import swap. Out of scope for this bounded pass
(other rows in the same TSV were plain shadow-vs-import swaps).

## Unblock condition

Rewrite the spec against the real `src/compiler/35.semantics/narrowing.spl`
API, including at least one exercise of `analyze_condition` with a real
`HirExpr` fixture for each `NarrowingCondition` variant (nil-check,
exists-check, is/is-not, truthiness), and `negate_facts`/`_combine_facts`.
