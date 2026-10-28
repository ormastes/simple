# SCV GitHub topic writer v1

## Boundary

The gateway owns publication to one topic branch derived from the authenticated
repository, principal, and request identity. The client sends the frozen
candidate data and its prepared-envelope digest; it does not choose a Git URL,
command, or destination ref. Host policy supplies the exact GitHub repository,
canonical HTTPS remote, storage roots, principal, and the separate
`allow_topic_publish` capability.

The topic writer first revalidates the durable preparation receipt and
reconstructs the verified candidate through the Git candidate owner. It
persists a topic-push intent before network effects. It then checks the
configured base ref, reads the derived topic ref, and invokes one Git push
through the owned candidate transport helper. The helper permits only
`refs/heads/scv/<32 lowercase hex>` and uses the explicit empty-expected
`--force-with-lease=<ref>:` guard. That condition makes the server reject a
topic ref created by a competing writer, including when that ref is an
ancestor of this candidate. There is no force fallback.

The gateway reads the topic ref again after every attempted push, including a
failed or ambiguous process result. It reports `topic_branch_published` only
when the authenticated response matches the configured numeric repository ID,
exact selector, and candidate OID. A known different head is
`topic_ref_conflict`; unreadable or missing post-write state is
`upstream_unknown`. Every response carries `publication: not_acceptance`.

## Module ownership

`gateway_github_topic_v1.spl` owns host policy checks, derived refs, durable
topic intent/result records, the typed observation contract, bounded GitHub
ref reads, and the live orchestrator. `db/git_candidate.spl` remains the only
owner of registered candidate validation, Git environment/config checks, and
the bounded Git process that creates the topic ref. The HTTP service dispatch
in `gateway_publish_service_v2.spl` authenticates first and derives both
storage and topic-write scope from host policy.

The injected I/O port exists for isolated BDD fixtures. Production dispatch
constructs the port from the authenticated GitHub reader and the candidate
owner helper; no port, authority flag, URL, or command comes from the request.

The additive `landing-reconcile` method is separately gated by
`allow_landing_reconcile` and `allow_landing_observation_write`. Its reader uses
only the configured numeric repository, the deterministic topic head, and the
configured protected base. It validates raw bounded GitHub responses, pages
through the complete PR result set, checks repository identity before and
after, and persists each exact observation under a digest-derived immutable
outbox key. An open PR is `review_pending`; a closed unmerged PR is
`closed_unmerged`; missing, ambiguous, incomplete, or inconsistent evidence
stays explicit.

A merged PR is currently only `observed_merged_needs_validation`. The gateway
does not yet own required-check verification, protected-ref ancestry proof, or
an admitted native history importer, so it cannot emit
`upstream_accepted`/`accepted_result_imported` or claim an accepted result.

## Concurrency and limits

The topic creation is an atomic absent-ref condition at the Git server. The
expected base head is checked immediately before the push, but it is not an
atomic base-branch CAS and may advance after that read. The topic ref proves
only that an exact candidate commit is reachable by the derived branch. It
does not prove acceptance, settlement, merge, protected-branch admission, or
production TLS service availability.

Each live ref observation performs three bounded GitHub API calls: repository
identity, ref lookup, and repository identity again. A publish attempt may
perform up to three observations. Process invocation and response limits come
from the fixed read policy. Live GitHub credentials remain gateway-host-owned;
no credential is accepted or returned in the protocol.

Landing reconciliation separately bounds discovery to eight pages of 100 PRs,
fetches strict detail only for a unique match, reads the configured protected
ref, and rechecks numeric repository identity. Exhausting the page bound is
`upstream_unknown`; an empty result is `landing_not_found` only after a complete
scan and successful identity/ref readback. A separate configured request
budget permits 4–12 authenticated API calls, preserving the existing three-call
read contract. The scan remains unknown if it cannot complete within budget.

## Qualification

The executable spec uses local bare repositories and injected read faults; it
does not contact GitHub. Runtime tests, live credential qualification,
production TLS, latency/RSS measurements, and production service admission are
`NOT_RUN`.
