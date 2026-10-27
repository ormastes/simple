# SCV GitHub topic writer v1 detail design

## Request and policy

The v2 publish request reuses the prepared candidate envelope: repository ID,
stable request ID, expected base ref/head, candidate OID and raw commit bytes,
message hint, frozen files, and prepared-envelope SHA256. No URL, refspec,
Git command, token, or write-capability field is accepted from the caller.

The service authenticates the bearer token first, verifies gateway and policy
repository identity, decodes bounded SDN, and constructs an admitted scope from
host policy. Topic publication requires `allow_topic_publish` independently of
`allow_prepare` and requires both read and write access to the scoped outbox.
The live wrapper accepts only the configured canonical GitHub HTTPS remote.

## Operation

1. Recompute the deterministic topic ref from repository ID, principal, and
   request ID: `refs/heads/scv/<first 32 lowercase SHA256 hex>`.
2. Ask `scv_gateway_github_publish_candidate_for_outbox_v2` to revalidate the
   durable preparation receipt and byte-for-byte envelope, then restore the
   raw commit and frozen tree through the candidate owner.
3. Store the immutable `topic_push_intent` record and verify its durable receipt.
4. Read the topic ref. Exact candidate OID is an idempotent published result;
   a different OID is a conflict; an unreadable response stops without push.
5. Read the base ref and require the expected OID. This check is immediately
   before the write but is not an atomic CAS on the base branch.
6. Invoke the candidate owner’s single-ref create helper. Its explicit
   `--force-with-lease=<topic-ref>:` protects the absent-ref condition. It
   refuses a competing branch even when the branch points to an ancestor.
7. Read the topic ref after every attempted write. Exact repository identity,
   selector, and OID are required for `topic_branch_published`, even if Git’s
   process response was lost.
8. Store a stable outcome record. Transport response details remain in the
   immediate result only, so a retry with the same state has identical bytes.

## State outcomes

| State | Meaning |
|---|---|
| `topic_branch_published` | Exact candidate OID observed at the exact derived ref in the configured numeric repository. |
| `topic_ref_conflict` | The derived ref exists at a different OID; no update is attempted after preflight, and guarded create cannot replace it in a race. |
| `base_changed` | Expected base no longer matches immediately before the write. |
| `upstream_unknown` | Post-write readback is missing, malformed, mismatched, or unavailable; no success is claimed. |

All states use `publication: not_acceptance`. They do not import, accept,
settle, merge, or update protected branches.

## External observation

Each live ref observation performs bounded `gh api` GETs for repository
identity, the requested ref, and repository identity again. A ref 404 is treated
as absent only after the same numeric repository ID, owner, and name succeed
before and after. Authentication failures and malformed responses do not
create an absent observation. Responses are byte-bounded and JSON depth-limited.

## Evidence boundary

Local bare-repository BDD scenarios exercise the candidate owner’s actual Git
transport and the gateway’s fake authenticated read port. They do not contact
GitHub. Native Simple execution, generated-manual verification, real GitHub
credentials, live branch mutation, production TLS, and production qualification
remain `NOT_RUN`.
