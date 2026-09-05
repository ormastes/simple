# narrowing_spec.spl shadows NarrowingContext/Fact/Scope — real narrowing algorithm untested

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**STATUS: RESOLVED 2026-08-10.** The spec was rewritten against the real
`compiler.semantics.narrowing` API with real `HirExpr`/`HirType`/`HirBlock`
fixtures. All local mirror types and the text-based re-implementation are gone;
`analyze_condition`, `negate_facts`, `_combine_facts` (via the `and` arm) and
`definitely_terminates` are now executed directly. Every previously existing
example's intent was ported (none dropped), and coverage was extended to the
variants that had none: `nil != x` operand order, unknown symbol, `is` /
`is not`, `a and b`, `not (x == nil)`, untyped-RHS `is`, and `IsCheck`
negation.

Verdict, both duplicate legs, byte-identical content, measured on a
purpose-built binary (`cargo build --release -p simple-driver`, private
`CARGO_TARGET_DIR`, mtime 2026-08-10 21:41:24 UTC — i.e. newer than the
21:31 `checker_check.rs` enum-type-name fix, and newer than the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` at 11:06):

- `test/unit/compiler/semantics/narrowing_spec.spl` — `Results: 31 total, 31 passed, 0 failed`
- `test/01_unit/compiler/semantics/narrowing_spec.spl` — `Results: 31 total, 31 passed, 0 failed`

Oracle non-vacuity was proven by sabotage: mutating two expected values in a
copy of the spec produced `Results: 31 total, 29 passed, 2 failed`, exit 1.

**No defect was found in the real narrowing algorithm once exercised** — the
implementation matched every ported assertion. That is a real (negative)
finding, not a vacuous pass: the sabotage run shows the assertions bite.

---


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
