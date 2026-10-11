# HIR loses imported enum owner for composite field subjects

**Status:** Reproduced; narrow `expression_core.spl` repair in review.

The native HIR lowering path classifies bare enum names in an or-pattern using
its subject's enum owner. For field subjects whose base is itself a nested
field, call result, or collection index, the field-expression path only asks
`_hir_expr_symbol_or_invalid` for a `Var`/`NamedVar`. Those composite expressions
have no direct symbol, so the field type remains unknown. The later pattern
lowering then treats `Deref` as a binding and reports
`or-pattern alternatives must bind the same variables: [Deref] vs []` for the
valid mixed arm `Deref | Field(_)`.

The isolated native matrix at
`test/fixtures/compiler/or_variant_binding_probe/` distinguishes these paths.
Against source `a487584ced2f4000fdc9c7ce7be1b441fa6150a5` and producer SHA256
`c6ce4632bbc5e1a3045a8a514a0c6fe8545e4ec5eb4215d90a7b430564c432f3`, direct
typed enum parameters, the qualified control, and direct `Holder.kind` all
compiled and ran with the expected `1,1,0` results. `Holder.inner.kind`,
`make_holder().kind`, `holders[index].kind`, typed and inferred foreach values,
and `val alias = value` failed with `[Deref] vs []`. The explicit alias
`val alias: E = value` passed. These are separate first-loss paths; this
record covers only composite field expressions.

The accepted probe source is commit
`a681ad90cd37cce2811e7245ca85d09cf586a72a`, with per-file SHA256 receipts in
`probe_manifest.json`. The first attempted fixture snapshot had a harness issue:
provider modules containing only enums/records were rejected because native
build requires function or static data. That attempt is preserved under the
external diagnostic lane; a marker function was added to providers before the
accepted run. It was not a compiler HIR failure.

The fix must resolve an owner only from existing HIR type metadata, declared
symbol types, or a callable's declared return type, then query the existing
owner-qualified field table. It must keep the existing raw-symbol lookup first,
retain live-span re-rooting for returned field types, and never infer an enum
from a variant's short name. The native system regression is
`test/03_system/compiler/or_variant_subject_field_type_system_spec.spl`.
