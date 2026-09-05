# Parallel Commit Layer Expert

## Boundary

This layer validates child-created result envelopes and publishes canonical
state at its logical owner. The common engine proposes revision/token state;
the landed `ParentCommitOwnerV1` adapter also applies and verifies an
application payload-token root before publishing both roots. It does not
execute child work, infer access sets, or decode arbitrary application graphs.

## Authoritative sources

- `src/lib/common/structural/parallel_commit/commit_contracts.spl`
- `src/lib/common/structural/parallel_commit/access_contracts.spl`
- `src/lib/common/structural/parallel_commit/commit_engine.spl`
- `src/lib/nogc_async_mut/parent_commit_owner.spl`
- `src/lib/nogc_async_mut/parent_commit_inbox.spl`
- `test/01_unit/common/structural/parallel_commit_contract_spec.spl`
- `test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl`
- `test/03_system/feature/language/parent_commit_piped_result_spec.spl`

## Publication invariant

`ParallelCommitStateV1` stores only the current revision and snapshot token.
This is intentionally constant-size: do not retain every historic result envelope in
canonical owner state. Receipts carry the current batch's ordered task IDs,
sequences, and payload tokens. Validation/order remain a reference O(n²)
implementation and receipt storage is O(n).

`parallel_commit_publish_envelopes` must:

1. reject malformed owner state, stale bases, duplicate task/sequence identity,
   duplicate payload tokens in one batch, and conflicts;
2. finish all validation before constructing the next state;
3. leave revision and snapshot token unchanged on every failure;
4. admit an empty commit only as a no-op with the existing snapshot token;
5. advance exactly one revision and replace the snapshot token once for a
   successful non-empty batch;
6. produce the same receipt order for every completion permutation.

The function returns a proposed next value. `ParentCommitOwnerV1` is the landed
mutex-serialized local adapter for live `(revision, snapshot_token)` plus an
application payload-token root. Its candidate path independently applies the
receipt's canonical payload-token order, compares the complete candidate root,
and emits a before/after mutation receipt before one publication. Malformed,
stale, conflicting, or candidate-mismatch batches preserve both roots. Other
runtime/MDSOC owners must serialize or compare-and-swap the same transition
before claiming atomic publish.

## Still incomplete

- The common envelope engine intentionally does not apply application payloads.
  `ParentCommitOwnerV1` now implements the bounded payload-token-root adapter,
  but arbitrary typed application schemas/graphs and capability-authorized
  candidate construction remain open.
- CAS publication for other owners, candidate-root capability validation,
  application-specific mutation-receipt adaptation, access-range summaries,
  fixed-tree reduction application, and additional runtime/MDSOC adapters
  remain WP-15/WP-30 gates.
  Canonical receipt wire encoding, equality, SHA-256 identity, and malformed
  input checks are landed in `commit_receipt_codec.spl`; do not list them as
  future work.
- The process candidate path validates and decodes the complete frame batch,
  applies canonical payload tokens to an independent root, verifies the offered
  complete root, and publishes typed commit/mutation receipts. Focused unit
  source covers candidate mismatch, mixed malformed, and conflicting rollback;
  the system source adds real-child application and mixed-batch rollback, but
  it still needs an admitted native verdict.
- The focused native system spec is not admitted because the deployed Stage 4
  CLI fails its bounded `test --help`/source-check path with status 139. Its
  operator mirror is authored, not generated. Stage 2/3 may run only their
  explicitly supported direct-compile evidence; they do not authorize general
  `test`, `spipe-docgen`, or `sspec-maintain`. Resume the latter through an
  admitted Stage-4 test surface and never substitute the Rust seed. The primary
  process flow compares closed `parent-commit-piped-result/v1` typed evidence;
  this in-memory comparison does not manufacture retained provider provenance.

Update this skill together with the parent-commit contract, guide, execution
status plan, and focused spec.
