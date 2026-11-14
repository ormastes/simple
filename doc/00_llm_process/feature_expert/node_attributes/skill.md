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

## Async registered initialization (P3, 2026-11-14)
`async <expr>` in value position parses (self-hosted `primary_expr.spl`) as
`async_init(<expr>)`, the producer binding the required-init verifier already
reads. `00.common/data/async_init_registry_v1.spl` wraps the existing
`phase_cell_*_v1` write-once cells (no second state machine) with a producer
type check (`E_ASYNC_INIT_TYPE`), an epoch fence (`E_ASYNC_INIT_STALE`) and a
zero-slot guarantee for nodes with no pending field. Specs:
`test/01_unit/compiler/data/async_init_registry_v1_spec.spl`,
`test/01_unit/compiler/hir/async_ctor_arg_parse_spec.spl`. Open: readiness
analysis (`E_ATTR_NOT_READY`), scheduler waiters, Rust seed parser.
## Immutable<T> read-only view (P2a, 2026-11-14)
`Immutable<T>` lowers to `T`; the declaring param/local symbol is recorded in
`HirLowering.immutable_view_symbols` and a field/index write rooted at it is
`E_IMMUTABLE_WRITE` (`hir_lowering/statements.spl` `flag_immutable_view_write`).
Other mutable aliases still write and the live view sees it (IMM-02). Spec:
`test/01_unit/compiler/semantics/immutable_view_write_spec.spl`. Untracked yet:
view aliasing, mutating methods, `.immutable()`, return/field positions.

## RevisionImmutable<T> / FrozenImmutable<T> handles (P2b, 2026-11-14)
Same lowering as `Immutable<T>` (`is_read_only_handle_name`, symbol -> handle
name in `immutable_view_symbols`). Writes are `E_IMMUTABLE_WRITE`; a `var` bound
directly from a revision/frozen handle is `E_FROZEN_ALIAS`. Spec:
`test/01_unit/compiler/semantics/revision_frozen_immutable_spec.spl`. W8 still
owns revision lease/cache identity, class detached-copy producers and the frozen
codec kind.
