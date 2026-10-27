# Schema-aware textual DB solver adapter

Status: implemented draft proposal route; runtime verification **NOT_RUN**.
Scope follows the SCV SDN solver gateway masterplan §§6–7 and 9–11, especially
R02 (separate domain solvers) and R11 (stable column identity).

The public `std.scv.solver_db_adapters_v1.solve_db_rows_schema_v1` entrypoint
accepts exact submitted snapshot/patch text and independently accepted policy,
original/current schema catalogs, historical V1 binding and policy revision.
Its dedicated profile is `db-rows-schema-v1`, under the existing `db.rows`
parser/model/reducer provider family. A source provider is refused by host
preflight. Candidate text never supplies its own accepted routing or policy.

This route supports an **original-schema snapshot**, one table, and V1
`UpdateFields` operations under matching `ScalarConflict`/`scalar-conflict-v1`
policies. It is not a current-schema snapshot rebase, CLI command, transaction
publisher, NULL importer or executing-provider admission mechanism.

The host binding hashes all three exact input texts. `identity_map_revision`
binds the complete original/current schema bytes and the historical V1 binding.
The original patch remains signed over its original names, schema stamp,
preconditions and payload. The strict existing snapshot, patch and policy
readers reject malformed or unpinned input. Every outcome retains the submitted
texts, including parser failures, cancellation and resource refusal.

Before reduction, all original row fields, policy fields and constraint fields
must map to known columns. Every edited field is resolved by the existing V2
migration owner into a `DbCellEditV2` with stable table/row/column identity.
Unsupported types, policies, defaults, constraints, nullability or identity
transitions require explicit inputs/migration. A dropped column cannot regain
its old data by reusing its name or UID.

The existing `db_plan_patch` previews the **unchanged authored patch** against
the original-schema snapshot and policy. It retains scalar conflict records
and checks the original transaction-wide uniqueness/reference constraints.
Only a conflict-free preview projects field names to the current schema by
ColumnUid, preserving values, row identities, row revisions and batch history.
The projected snapshot gets a fresh content revision. Independent nullable or
constant-defaulted additions retain their schema definitions; old rows gain no
invented cells or eagerly applied defaults. V1 only represents Absent/Value;
the separate V2 Null/Defaulted/Tombstoned states are not collapsed or imported.

The candidate digest binds both the full schema mapping identity and projected
snapshot digest. Host-owned required checks still include patch-signature
admission, causal closure, combined DB constraints and schema UID mapping.
Constraints added to new columns or changes to existing column definitions
block this bounded adapter. Even unchanged constraints require independent
whole-candidate validation; a reducer preview is not settlement evidence.

Input lengths, typed metadata, schema/row counts and projection search products
are budgeted before their respective operations. Repeated digest checks in the
existing edit adapter are explicitly charged. Provider execution remains
`unqualified-builtin-execution`, status `needs_inputs`, empty deterministic
result key and `external-validation-required`; no startup/performance or native
execution claim is made.

BDD specification: `test/02_integration/lib/scv/solver_db_rows_schema_v1_spec.spl`.
Its first seven scenarios and fixture were committed before implementation in
`2c26619c035`; later adversarial cases extend the same executable spec. No
admitted general pure-Simple runtime was available, so RED/GREEN, SPipe docgen,
manual maintenance, branch coverage, core/MCP smoke and performance checks are
**NOT_RUN**, with no Rust-seed fallback. The authored manual is a review aid,
not generated execution evidence.
