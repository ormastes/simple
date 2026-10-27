# SCV GitHub gateway publication preparation v2

Executable scenarios: [scv_gateway_github_publish_v2_spec.spl](../../../../../../test/03_system/app/scv/feature/scv_gateway_github_publish_v2_spec.spl)

## Covered behavior

- The authenticated v2 HTTP handler maps one configured bearer identity to a
  host-owned repository and principal scope. The request cannot select a
  principal, remote URL, filesystem path, or Git command.
- Preparation reads the configured base ref and requires its exact expected
  head. It verifies the supplied raw commit OID and reconstructs its tree from
  the frozen text-file snapshot through `db_git_candidate_restore`.
- The outbox envelope binds the repository identity, principal, request ID,
  base ref and head, deterministic topic ref, candidate OID, exact commit bytes,
  and the snapshot projection digest. The envelope is persisted through the
  existing scoped draft blob owner; the `export_prepared` response follows its
  durable intent/object/receipt checks.
- Same-request retries preserve identical bytes and reestablish the durable
  receipt. A retry can recover after the mutable base ref advances because its
  immutable expected base object is still verified. A divergent envelope is
  rejected.
- Reconciliation requires authenticated read scope, the supplied envelope
  digest, exact stored bytes, a reconstructed candidate, and GitHub readback
  of the configured repository, generated topic ref, and exact candidate OID.
  Read failure or mismatch stays `upstream_unknown`.

## State boundary

`export_prepared` is a local durable outbox result. `topic_branch_published`
means reconciliation observed the exact branch ref and candidate OID from the
configured read provider; this service did not publish it. `upstream_unknown`
means readback did not establish that exact state. Every response carries
`publication: not_acceptance`. No state here means upstream acceptance, a
merged PR, or imported accepted results.

The host policy keeps `allow_prepare`, `allow_reconcile`, and
`allow_topic_publish` separate. This slice enables only the first two; a topic
publisher requires its own explicit host grant.

The reconciliation read path verifies the immutable object bytes but does not
reissue or prove a local durable receipt. The preparation and retry paths do
reissue the draft store `put` and verify the returned durable receipt before
acknowledging `export_prepared`.

## Qualification

Native SSpec execution: **NOT_RUN**. No admitted Simple runtime was available
for this lane. The implementation remains a development-loopback service;
production TLS is unqualified. This increment has no GitHub write operation or
settlement receipt authority, so it does not advance `DbSettlementJournal` or
claim acceptance.
