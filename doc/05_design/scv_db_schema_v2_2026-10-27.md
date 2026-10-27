# SCV database schema V2 local implementation

Owner: `/root/impl_database_schema`, branch `work/scv-impl-db-schema-20261027`.
Base: `25cdeee5d5da8f8c7c3ab530d43bc2fd4a360d26`, target `release/1.0.0`.
Scope: source implementation of the first local SCVN-D01/D02/D03 wave under
REQ-002, REQ-004, REQ-005 and REQ-014. This is not completion of those tasks or
the 65-task objective. Runtime, generated manuals and admission remain pending.

## Owners and callable contracts

| Owner | Public entry points |
|---|---|
| `src/lib/scv/db_schema_identity_v2.spl` | V2 records/enums, schema/UID/default/type/address validation, UID lookup |
| `src/lib/scv/db_schema_codec_v2.spl` | `db_schema_create_v2`, `db_schema_bytes_v2`, `db_schema_revision_v2`, `db_schema_seal_v2`, `db_schema_check_revision_v2`, column/operation digests, address wire encode/decode, cell state bytes |
| `src/lib/scv/db_schema_merge_v2.spl` | `db_schema_apply_v2(schema, operation) -> Result<DbSchemaV2,text>`; `db_schema_merge_v2(base,left,right) -> Result<DbSchemaMergeResultV2,text>` |
| `src/lib/scv/db_schema_migration_v2.spl` | Exact-original-schema field/UID/edit adapters, reviewed mapping envelope, lazy introduction-default interpretation |

`DbSchemaV2` owns `table_uid`, `table_name`, `parent_revision`,
`merge_parent_revision`, `revision`, `columns`, `applied_operations`, `tombstone`.
`DbColumnDefinitionV2` owns UID/name/type/nullability, future-write default,
immutable introduction default/revision/migration UID, constraints, merge policy,
visibility, presentation order and tombstone. `DbCellAddressV2` is exactly
`(table_uid:EntityUid,column_uid:EntityUid,row:EntityRef)`.

All identities reuse existing EntityUid validation, kinds and namespace. Table,
column, constraint and migration UID kinds are checked at their typed boundary.
Callers supply already allocated offline UIDs. There is no UUID alternative,
alias allocator, publisher, persistence adapter or authority decision here.

## Canonical identity and immutable proposals

V2 records use existing `db_frame`, canonical text/list/map/set and SHA-256.
Domains contain `v2` and schema payloads include discriminator `2`; the existing
outer `db_domain_bytes` envelope remains unchanged. Signed DbPatch V1 and DbValue
serialization are untouched. Schema revisions exclude their self-referential
revision field, include parents, definitions and operation receipts, and sort
UID-addressed maps. Physical column array order does not supply identity.
Presentation order is an explicit revision-bearing attribute.

Typed operations require exact base revision and expected definition digest.
Same migration operation UID and canonical payload acknowledges replay even
after descendants; divergent payload reuse rejects. Dependencies require prior
receipts. Add/Rename/Drop/Move/Alter/SetDefault/SetNullability/SetMergePolicy and
constraint add/drop have explicit variants. Create-table is a typed constructor.
Drop retains a terminal column tombstone. Recreate requires a distinct caller
allocated UID. Base tombstones cannot become live even through independently
sealed solver inputs. Introduction stamps/defaults cannot be rewritten.

Three-way merge combines independent additions; same-name distinct-UID columns
conflict even when their apparent definitions match. Concurrent changes to one
definition conservatively conflict unless one side equals base. Same UID with
different new definitions conflicts. Drop/edit and incompatible rename races
retain all three input schemas and return no candidate. Invalid input revisions
return an error; the host must retain the original input objects on every error.

A returned candidate is a proposal. `required_checks` always contains schema
identity, combined-row constraint closure and old-schema compatibility. Constraint
reference checks here do not establish uniqueness, foreign-key validity or
cross-row transaction safety. Parent host validators must check the combined
snapshot and exact read set before admission. No success here settles aliases.

## V1 adaptation and defaults

`db_schema_adapt_v1_field_v2(original,current,original_revision,row,name)` checks
the exact original schema digest and resolves the name only in that original
schema; it never falls back to current names or array positions. Same-UID rename
and presentation moves preserve the mapping; dropped/recreated UID fails.

For actual legacy patches, `DbV1SchemaBindingV2` binds the V1 revision label to
the exact original V2 identity catalog using `db_schema_v1_binding_digest_v2`.
The host supplies this binding from admitted historical metadata. A binding
digest proves integrity, not historical authority. `db_schema_adapt_v1_edit_v2`
validates the legacy patch digest and membership of the exact row/field/before/
after edit, then returns `DbCellEditV2` with both authored and target schema
revisions. Signature authentication and row preconditions remain the original
admission/reducer responsibilities; no legacy batch bytes are rewritten.

`DbCellStateV2` separates absent, null, explicit value, stamped defaulted value
and tombstone without extending the V1 enum. `db_schema_lazy_cell_v2` supplies
the immutable introduction constant only when the column did not exist in the
row's pinned original schema. Existing-column absence is never reinterpreted
under a later future-write default. A stored default must match the column's
exact introduction value, migration UID/namespace and revision. Explicit null
requires nullable; absent required values reject.

Supported first-wave types are `text`, `u64`, `bool`, `entity_ref`, `list`, `set`,
`observed_set`, `causal_set`, matching the existing value vocabulary. Defaults
are checked against both future and introduction types. Unknown/custom types
are explicitly unsupported. There is no dynamic/clock/random default variant.
Changing type, tightening nullability, or changing field policy requires reviewed
migration/backfill evidence and fails closed here. Reviewed envelopes pin source,
target, column mappings and review digest; they authenticate no reviewer and do
not execute cross-type or identity conversions. Those paths remain explicit
`*_EXECUTION_REQUIRED` outcomes pending a separate evaluated migration owner.

## Authored evidence and pending gates

Executable scenarios: `test/02_integration/lib/scv/db_schema_v2_spec.spl`.
Reusable fixtures: `test/fixtures/scv/db_schema_v2_fixture.spl`.
The main local scenario creates two offline actors' distinct columns, merges,
renames an existing column, and adapts the exact old-schema row edit to its UID
while checking legacy bytes/digest/signature preservation. Negative scenarios
retain colliding/dropped drafts, reject tombstone resurrection, forged defaults,
wrong types, wrong pins, unsupported coercions, stale bases and divergent replay.

All runtime `check`, test, native, docgen and sspec-maintain commands are
**not_run**: no admitted self-hosted runtime was available to this lane. No seed,
bootstrap fallback or generated passing manual was used. The parent owns runtime
discovery, host/vertical integration, admitted schema history and independent
validation. Required full-library/compiler/MCP checks and generated-manual review
remain pending. No coverage percentage, performance result or production PASS
is claimed. First-wave storage is bounded to 4096 columns and 16384 receipts;
lookup/merge/uniqueness checks are quadratic at those bounds. Large-schema/index
performance targets remain unmeasured and need a separate indexed owner.

Rollback: remove these new V2 modules and their new fixtures; no existing wire
format, reducer, store, compiler, CLI or configuration owner was changed.
