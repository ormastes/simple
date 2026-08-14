# Parallel Commit Layer Expert

## Boundary

This layer validates child-created result envelopes and publishes one canonical
snapshot root at its logical owner. It does not execute child work, infer access
sets, decode payloads, or mutate an application snapshot in place.

## Authoritative sources

- `src/lib/common/structural/parallel_commit/commit_contracts.spl`
- `src/lib/common/structural/parallel_commit/access_contracts.spl`
- `src/lib/common/structural/parallel_commit/commit_engine.spl`
- `test/01_unit/common/structural/parallel_commit_contract_spec.spl`

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
mutex-serialized local adapter for live `(revision, snapshot_token)`
publication; other runtime/MDSOC owners must serialize or compare-and-swap the
same transition before claiming atomic publish.

## Still incomplete

- The application owner must build and verify the candidate snapshot before
  passing its token; payload application is not implemented by the common
  envelope engine.
- CAS publication for other owners, candidate-root capability validation,
  mutation-receipt adaptation, access-range summaries, fixed-tree reduction
  application, and additional runtime/MDSOC adapters remain WP-15/WP-30 gates.
  Canonical receipt wire encoding, equality, SHA-256 identity, and malformed
  input checks are landed in `commit_receipt_codec.spl`; do not list them as
  future work.
- The process path validates and decodes the complete frame batch before
  calling the owner transition, but no application-owned candidate payload is
  applied or verified yet. Mixed valid+malformed/conflicting rollback must prove
  both revision/token and application root remain unchanged.
- The focused native system spec is not admitted because the deployed Stage 4
  CLI fails its bounded `test --help` probe with status 139. Repeat it only
  after a fresh admitted redeploy; never substitute the Rust seed.

Update this skill together with the parent-commit contract, guide, execution
status plan, and focused spec.
