# SCV GitHub topic writer v1

**Evidence class:** local host fixture; no live GitHub writes.

The gateway publishes a prepared SCV candidate to the branch derived from the
authenticated repository, principal, and stable request ID. It rechecks the
durable preparation receipt, records a durable topic intent, and uses the
candidate owner’s create-only ref guard for one `refs/heads/scv/<hash>` ref.

## Primary flow

1. Prepare a candidate and its frozen file snapshot.
2. Persist and verify the immutable topic intent.
3. Confirm the expected base and that the derived topic is absent.
4. Create the topic with Git’s explicit empty-expected ref lease.
5. Read back the exact repository, ref, and candidate OID.
6. Report `topic_branch_published` with `publication: not_acceptance`.

The Git transport scenarios use a temporary bare repository. The authenticated
GitHub port injects raw JSON responses into the same strict decoder used by
the live provider. No credentials or live service are used.

## Failure and retry flow

- An existing different topic head returns `topic_ref_conflict` without an
  overwrite attempt.
- A topic created by a competitor after the absent check is rejected by the
  empty-expected lease, even if its OID is an ancestor.
- A lost Git acknowledgement is reconciled by exact post-write readback.
- An exact retry returns the published state without a second push.
- Missing durable state, missing host topic capability, or missing bearer
  authentication fail before Git write.
- Unreadable or mismatched readback returns `upstream_unknown`.

## Landing observation

1. Send `landing-reconcile` through the authenticated service with the exact
   prepared envelope.
2. The gateway reopens and validates the durable candidate before querying
   the configured numeric GitHub repository for its generated head and
   configured protected base.
3. The provider verifies the numeric repository identity before and after,
   follows at most eight pages, fetches unique PR detail, and reads the current
   protected ref.
4. A complete empty result is `landing_not_found`; one open PR is
   `review_pending`; a closed unmerged PR is `closed_unmerged`; several matches
   are `landing_ambiguous`.
5. An exact merged PR is durably recorded as
   `observed_merged_needs_validation` with the actual merge SHA and protected
   ref SHA. This is an observation only, with `publication: not_acceptance`.
6. An identical retry reuses its digest-derived observation ID. A changed
   authority snapshot receives a distinct ID.

Fork heads, changed head OIDs, a different base, malformed merge fields,
transport failure, changed repository identity, or incomplete pagination stay
`upstream_unknown`. Required checks, protected-ref ancestry, actual merged tree
verification, and native history import have no admitted owner yet; consequently
`upstream_accepted` and `accepted_result_imported` are not emitted.

**Generated-manual check:** NOT_RUN because no admitted Simple runtime is
available. The executable spec remains the source of test behavior.
