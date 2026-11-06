# HIR frontend diagnostics: Any-alias message and cross-module inferred fallback (2026-10-30)

Status: open
Area: compiler/35.semantics/lint/hir_frontend_diagnostics.spl

## 2026-11-07 source investigation and narrow repair

Any-alias repair authored; runtime qualification **NOT_RUN**. The current
`hir_lowering/statements.spl` transports initializer types through
`binding_payload_type` into the non-optional `HirStmtKind.Let` type slot even
without a source annotation. Consequently `any_note_let` took its `Any` branch
and returned before recording the alias. It now retains immediate alias origin
when the written-Any scanner does not identify an explicit annotation. Typed
use reporting prefers that specific alias origin over a generic pending reason.
The original alias regression is enabled, with chained-alias and explicit-Any
negative cases. This does not establish an executed PASS or close this issue.

Cross-module fallback remains open and its pending cases are unchanged.
`note_let` likewise treats every non-`Infer` binding payload as an annotation;
the canonical direct-call binding transport can supply `Any`, `Error`, or a
named return type without an annotation. Independently, imported callable
projection now resolves qualified type symbols in
`hir_lowering/_Items/module_callable_types.spl`; older assumptions about a
third-module type necessarily being erased must be checked against actual HIR
layout authority. A follow-up needs explicit source-annotation provenance (or
another canonical annotation receipt), plus resolved versus genuinely missing
foreign-layout controls. Removing the annotation guard alone would regress
the annotated-binding exclusion. No HIR schema or codec change is included in
this narrow repair.

### Annotation provenance follow-up (authored, NOT_RUN)

The approved follow-up retains `local_annotation_provenance: Dict<i64, bool>`
on `HirModule`, keyed by the canonical local `SymbolId.id`. True means an
explicit AST annotation, false means an inferred declaration, and absence is
unknown. `hir_local_annotation_state` returns 1/0/-1 respectively. No module
completeness flag is asserted. The four ordinary val/var lowering branches
record their actual `has_annotation` decision after symbol definition;
synthetic and destructured binders without a proven receipt remain unknown.
The map resets at module lowering entry, is copied into both module-build
outputs, and is copied independently by method resolution and the finite HM
typed-module owner. Synthetic empty/layout-only modules default to unknown.
The codec owner separately updates both formats and their cache admission
versions; old-cache absence is not evidence of an inferred declaration.

`note_let` now classifies only proven inferred declarations, and local Any
alias handling uses the same exact metadata. The pre-existing written-Any
scanner remains a presentation/suggestion input, not local binding authority.
Qualified retained struct/class/enum layouts now establish known return types
even when the caller does not directly import the type's defining module.

Enabled tests cover the exact foreign return symbol/layout, genuine Any-return
fallback, explicit annotations, shadowed same-name locals, var producers,
unknown legacy metadata, and independent map copies. Historical pending
third-module warning cases are left intact pending executable confirmation of
their now-conflicting expectations; they are not counted as passing evidence.
This source repair and its metadata/codec integration require the admitted
runner before the bug can be closed.

## Symptom

- `test/01_unit/compiler/lint/frontend_diag/any_warn_rules_acceptance_spec.spl`, example "flags an
  unannotated alias of an Any value": exactly one W-HIR-INFER-003 is emitted, but its message lacks
  "it is initialised from `b`". The alias branch at `hir_frontend_diagnostics.spl:687` is not taken
  for `val c = b` when `b` is an `Any` parameter.
- `test/01_unit/compiler/lint/frontend_diag/inferred_type_fallback_use_spec.spl`:
  - two examples fail with `array index out of bounds: index is 0 but length is 0` (imported fn
    returning a third-module struct)
  - "still fires when only the facade FUNCTION is imported..." finds 0 instead of 1

## Root cause

Not isolated. The parameter-symbol registration in `any_syms` does not seem to cover `Any`
parameters, and the cross-module return-type fallback path finds no findings and indexes an empty
list. Both need a debugging pass on the HIR diagnostics walker.

## Unblock

Fix the walker. Then remove the `pending` markers that link here.
