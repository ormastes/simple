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
