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
GitHub read port is injected for deterministic host tests. No credentials or
live service are used.

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

**Generated-manual check:** NOT_RUN because no admitted Simple runtime is
available. The executable spec remains the source of test behavior.
