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
## Async registered initialization (P3, 2026-11-14)
`async <expr>` in value position parses (self-hosted `primary_expr.spl`) as
`async_init(<expr>)`, the producer binding the required-init verifier already
reads. `00.common/data/async_init_registry_v1.spl` wraps the existing
`phase_cell_*_v1` write-once cells (no second state machine) with a producer
type check (`E_ASYNC_INIT_TYPE`), an epoch fence (`E_ASYNC_INIT_STALE`) and a
zero-slot guarantee for nodes with no pending field. Specs:
`test/01_unit/compiler/data/async_init_registry_v1_spec.spl`,
`test/01_unit/compiler/hir/async_ctor_arg_parse_spec.spl`. `E_ATTR_NOT_READY` (2026-11-15): an unawaited read `n.f` of a field bound with
`f: async <expr>` at a construction of local `n` in the same function; error in
every gate mode; implemented in the `RequiredInitCollectorV1` visitor of
`required_field_init_v1.spl`, spec `test/01_unit/compiler/hir/attr_not_ready_v1_spec.spl`.
Open (see `doc/08_tracking/bug/immutable_async_open_questions_2026-11-15.md`):
non-await readiness
proofs, alias flow, scheduler waiters, Rust seed parser.
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

## Revision hooks and capability escape (2026-11-15)
REV-02: the pointer-free frozen payload is `FileAstV1` via
`canonical_file_ast_encode_v1`/`decode_v1`; round-trip, determinism and rejection
pinned by `test/01_unit/compiler/cache/rev02_frozen_file_ast_codec_spec.spl`
(5/5; the codec had no spec before). REV-01: reclamation hook is the SCV reader
lease (`scv_compile_snapshot_lease_*`); `test/01_unit/lib/scv/rev01_pinned_revision_lease_spec.spl`
is 1 GREEN, 1 RED (a process holds one lease, so several pinned revisions are
not protected; bug `rev01_one_lease_per_process_blocks_multi_revision_pin_2026-11-15`).
`E_INIT_CAPABILITY_ESCAPE` (owner rule 2026-11-15): the `async_init(...)` producer
may only receive IMMUTABLE input. Default off, `SIMPLE_INIT_CAPABILITY_ESCAPE=on`
rejects any `var` binding, `mut T` parameter, `me`-method `self`, `Ref`/`Ptr`-typed
binding or closure capture of those, nested anywhere in the argument
(`InitCapabilityScanV1`; `init_capability_escape_v1_spec`, 12/12). `val x = counter`
then `async_init(x)` is accepted.

## Backing layouts + AoS/SoA (2026-11-16)
Placements are now `direct | column | array_index | sparse_hash`, plus `array_ptr | hash_ptr`.
The two pointer tokens resolve, but construction returns `Err` (no safe stable
reference across growth/rehash; `TODO(node-attr-pointer-layouts)`).
`array_index` keeps the slot index on the node, through an `AttrOwnerV1<i64>`
index owner (`attr_store_indexed_v1`) or an internal `AttrIndexCellsV1` when
detached, and reuses retired slots from a free list.
Multi-field side arrays: `AttrGroupStoreV1<T>` with `AttrLayoutV1` `Aos | Soa`
(default soa), column/array_index only.
AST wiring (`nodes.spl`): mode 3 = array_index, `layout=aos|soa` key
(`expr_attr_side_layout()`); a pointer token turns the switch off.
Spec doc: `doc/07_guide/language/attributes/node_attribute_layouts.md`.
Matrix: `test/01_unit/compiler/data/attribute_layouts_spec.spl`.
