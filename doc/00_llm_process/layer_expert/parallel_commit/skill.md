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

The function returns a proposed next value. It is not a synchronization
primitive: a runtime/MDSOC owner adapter must serialize or compare-and-swap it
against the live `(revision, snapshot_token)` before claiming atomic publish.

## Still incomplete

- The application owner must build and verify the candidate snapshot before
  passing its token; payload application is not implemented by the common
  envelope engine.
- Serialized/CAS owner publication, candidate-root capability validation,
  mutation-receipt adaptation, canonical receipt hashing/wire encoding,
  access-range summaries, fixed-tree reduction application, and a runtime/MDSOC
  adapter remain WP-15/WP-30 gates.
- The focused spec currently passes only through a Rust bootstrap seed. Repeat
  it with an admitted Stage 4 self-hosted CLI before production acceptance.

Update this skill together with the parent-commit contract, guide, execution
status plan, and focused spec.
