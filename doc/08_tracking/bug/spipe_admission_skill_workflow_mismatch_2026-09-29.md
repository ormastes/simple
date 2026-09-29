# SPipe admission: skill, workflow, and wiki disagree

Observed: 2026-09-29. Project source inspected at `9b1460d30afeeb661e14b3c4f48a9fee362ee90c`.
Status: unresolved configuration/procedure mismatch, not missing user permission.

## Why the agent did not complete admission

The user explicitly authorized self-review and PR landing. GitHub author approval
is a different operation; the intended operation is the SPipe required status.
The installed `spipe:dev` 0.2.0 skill and the live
`spipe_self_review_guide` MCP response require a configured broker that authenticates
a canonical v2 policy database and an exact higher-model review receipt. They
explicitly reject a Simple workflow offering only `self_attestation`.

Current project configuration and workflow do not implement that route:

- `.github/review-admission-broker.json`: `configured: false`,
  `implementation_status: unsupported_until_external_signed_broker`, and
  `signed_receipt_protocol: unimplemented`.
- `.github/workflows/review-admission.yml` exposes `self_attestation`, constructs
  a `spipe-self-review-self-attestation/1` record, and sets
  `review_evidence_broker_authenticated: false`.
- The repository wiki's older handoff procedure instead recommends this legacy
  dispatch and PR-body edits to trigger admission. That advice conflicts with the
  installed skill and live guide. A green/skipped GitHub check alone does not
  establish the broker-authenticated receipt required by that guide.

`spipe_review_capabilities` advertises broker-only admission and explicit
user-authorization evidence. This describes the API contract, not proof that a
broker is configured. `spipe_self_review_privilege_evaluate` and
`spipe_self_review_approve` exist, but their closed request requires actual
receipt digests and authenticated policy; these must not be invented. For
Simple, the guide selects the trusted default-branch workflow instead of mixing
it with the generic MCP implementation.

## Observed outcome and agent mistakes

The normal exact-head merge of PR #2054 at
`99dd5686ddfe6ca0d09e56a87a158776d37c7b53` was rejected by branch policy.
The structural gate passed, but the required admission check was absent.
This does not mean the focused code review or tests were absent.

The agent should have invoked the canonical guide/capability tools before asking
the user for admission configuration. A worker also incorrectly dispatched the
legacy route for #2054; run `36507083231` was cancelled. An earlier legacy
run `36501161179` for #2045 completed before merge. Corrections were posted on
both PRs; neither dispatch is valid independent release-admission evidence.
No signatures, policy records, reviewer identities, or receipt digests should be
fabricated to make the API accept a request.

## Required resolution and next-session procedure

1. Run the canonical self-review guide, capture the live PR head, and perform
   the required exact-head review. Distinguish review evidence from admission.
2. Inspect current broker configuration and workflow inputs. Retain this report's
   dated evidence; do not assume the mismatch still exists after a repair.
3. The policy owner must align the wiki, installed skill, workflow, and actual
   broker implementation. Under the current guide, configure the pinned broker,
   signed v2 policy/trust data, authentic review/user-authorization receipts,
   and status expiry/invalidation before issuing admission.
4. Use exactly the selected implementation. Do not manufacture a body edit to
   obtain a skipped check, use admin merge, weaken protection, or substitute
   author GitHub approval. Do not silently upgrade plugin/submodule pins.
5. Recheck the exact head and required checks, then perform the normal merge.
   Bootstrap/test qualification and immutable RC1 promotion remain separate gates.

## Wiki write route

The Caret wiki search tool returned `centralized worktree storage is unavailable`.
This project-owned report is linked from the canonical repository wiki at
`doc/00_llm_process/llm_wiki.md`; no private account material was published to
SPipe common or another scope.
