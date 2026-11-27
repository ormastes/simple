# No lint flags `Option<T>` on the public surface (S-12)

**Status:** FIXED 2026-11-12 (P1) — `src/compiler/90.tools/lint/rules/robust_option_surface_rule.spl` registered in `static_rules.spl`; acceptance, reproducing and generalization specs green on the seed. P2+ residue (cross-file export closure, explicit accessor methods, `ROB-OPT-003`) stays listed under "Unblock condition".
**Severity:** Warning-tier policy gap (no runtime defect).
**Affected file:** `src/compiler/90.tools/lint/static_rules.spl:30-52` (rule table has no `robust_option_surface` row); `src/compiler/35.semantics/lint/semantic_api/checker.spl:51-52` (primitive walker is standalone, not an optional walker).
**Spec files:** `test/01_unit/compiler/semantics/robust_option_surface_spec.spl` (acceptance S-12); P1 adds `test/01_unit/compiler/lint/robust_option_surface_rule_spec.spl` (reproducing) and `test/01_unit/compiler/lint/robust_option_surface_generalization_spec.spl` (generalization).
**Design:** `doc/05_design/language/robust_types/robust_types_layer_contracts_2026-11-12.md` §2 `ROB-OPT-001`/`ROB-OPT-002`, §7, §9 S-12, §10 P1.

## Symptom

A `pub fn` parameter, a `pub struct`/`class` field (and so its generated
accessor), an in-file alias of `Option<T>`, a nested `List<Option<T>>` /
`(A, B?)` / `fn(Option<T>) -> R` and an in-file `export`ed declaration all
lint clean today.

## Unblock condition

A registered static lint rule `robust_option_surface` that walks each public
declaration once (one pass over aliases + declarations, no whole-tree
rescans), emits `ROB-OPT-001` for inputs and `ROB-OPT-002` for attributes at
`StaticLintLevel.Warn` only, and makes the acceptance spec green. Cross-file
`__init__.spl` export closure, explicit accessor methods and `ROB-OPT-003`
(return/local optionals) stay in P2+.
