# Node attributes feature knowledge

Consume the selected requirements in
`doc/02_requirements/feature/node_attributes.md`, the architecture in
`doc/04_architecture/compiler/node_attributes.md` and the detail design in
`doc/05_design/compiler/node_attributes.md` before changing source.

Full scope includes applying the feature to Simple's compiler and owner-managed
BuildRunner views. Land architecture/design first, then common structural
contracts before consumers. A standalone resolver or AST pilot is not completion.

Preserve existing AST owner arrays, canonical layout/collection/profile owners and
frozen identity/tag/transfer contracts. Managed attributes use exact nominal types
and whole-node obligations, not untyped tags or per-field NotInit wrappers.
Build-time off mode preserves ordinary programs; it cannot disable live safety.

Use one frontend grammar and checked-place contract across engines. Never infer
runtime/native/XRay support from an enum, accepted annotation, authored spec or a
different provider. Record admitted runtime lineage and source-matched execution.
The source audit and test matrix explicitly distinguish existing components from
missing integrated behavior and unexecuted acceptance tests.

## Status 2026-11-14 (lane nodeattr)
Placement API: `AttributeStoreV1<T>` in `src/compiler/00.common/data/attribute_schema_v1.spl`
(embedded owner delegate / dense column / sparse hash; token resolved once via
`data_attr_storage_resolve_v1`; default `direct` = owner behaviour; nothing in the
compiler builds one yet). Measured AST column census: `doc/05_design/compiler/data/node_tree_storage.md`
7.4 (note: `op` is only 7.9% dense over global node ids). Seed accepts field-level
`@attr_storage` after the parser fix in `types_def/mod.rs` (`is_at_field_annotation`).
Seed interpreter defect: `continue` in a `val x = match` arm yields nil; use statement-level match.
