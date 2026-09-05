# Scoped Self-Review Policy Database

This guide defines the operator-owned textual database used by `SPipe Self
Review Admission`. It governs protected PR integration only. It does not grant
release-environment approval, candidate admission, signing, publication, or a
GitHub provider Approve review.

## Storage and default

Store UTF-8 JSONL outside the repository and provide its exact bytes through
the `SPIPE_SELF_REVIEW_POLICY_DB` Actions secret. The PR worktree contains only
`.spipe/policy/self-review-policy.sdn`, a non-authoritative projection. Never
commit the live JSONL records, a signing key, or a provider token.

The first and only header line for an empty database is:

```json
{"schema":"spipe-self-review-policy-db/1","default_allow":true,"max_ttl_seconds":86400,"authority":"operator_owned_external"}
```

Within a valid authenticated database, no matching record means ordinary
reviewed code/text is eligible. Missing/malformed database bytes still fail
closed because explicit denies could not be observed.

## Record schema

Each following line is one closed `spipe-self-review-policy-db/grant/1` object.
Despite the historical `grant` schema segment, `effect` is only `deny` or
`constrain`; no record can broaden default eligibility.

```json
{"schema":"spipe-self-review-policy-db/grant/1","record_id":"deny-release-hardening-1","effect":"deny","repository":{"provider":"github","id":1175797696,"node_id":"R_kgDORhU_wA","name":"ormastes/simple"},"pull_request_number":28,"head_sha":"<40-or-64-lowercase-hex>","session_id":"feature/release-hardening","self_reviewer":{"provider":"github","identity":"2378857","model":"codex/gpt-5.6-sol","tier":"high_capability","effort":"xhigh"},"changed_paths_manifest_sha256":"<sha256>","review_evidence_sha256":"<sha256>","allow_scopes":[],"deny_scopes":[],"issuer":{"provider":"github","identity":"ormastes","key_id":"operator-key-1"},"issued_at_unix":1787846400,"expires_at_unix":1787847300,"previous_record_sha256":"<sha256-of-previous-record-line-or-64-zeroes>","signature":"<operator-detached-signature>"}
```

A matching `deny` rejects that exact repository/PR/head/session/reviewer and
receipt/manifest pair. A matching `constrain` requires every changed path to
match at least one `allow_scopes` item; any `deny_scopes` match rejects first.
Multiple matching constraints intersect.

Scope objects always contain both keys:

```json
{"kind":"code","path":""}
{"kind":"text","path":""}
{"kind":"file","path":"doc/guide.md"}
{"kind":"directory_files","path":"doc/07_guide"}
{"kind":"directory_recursive","path":"src/app/release"}
```

- `file` matches one exact file.
- `directory_files` matches immediate files, not nested children.
- `directory_recursive` matches descendants, not a similarly prefixed sibling.
- `code` and `text` use canonical classification; unknown extensions are code.
- Rename evaluates old and new names, delete old, copy new.

The first record uses 64 zeroes for `previous_record_sha256`. Each later record
uses SHA-256 of the exact prior JSONL record line. Records and decisions expire
within 24 hours. The external broker authenticates operator signatures before
setting the evaluator authentication fact; structural presence is not signature
verification.

## Explicit self-attestation

The user-authorized mode is explicitly `self_attested`, not authenticated
higher-model or independent review. Dispatch accepts the model/effort and the
literal `PASS:0:0`; the trusted default-branch workflow resolves repository,
PR, head, protected base, merge-base, diff, target ruleset, and actor before it
creates `spipe-self-review-self-attestation/1`. Caller text is never marked
broker-signed or independently authenticated. A future signed broker mode must
use a distinct `broker_signed` evidence value and actually verify its receipt.

## Decision and audit

`simple release self-review-plan` emits `spipe-self-review-decision/1`, the
policy/manifest/evidence digests, exact target/head/base/merge-base/diff,
session/reviewer, matched constraint record IDs, and a 10-minute expiry. It is
mutation-free and always emits
`provider_approval_claimed=false`. The default-branch workflow separately
creates `SPipe Self Review Admission` on the exact head and retains the
manifest, self-attestation, decision, and aggregate audit digest for 90 days.

The required check uses the generic GitHub Actions App identity by explicit
user policy. That identity is not independent security: a same-repository PR
workflow can potentially spoof the same context. The repository Actions
default is read-only and the intended emitter is gated by the
`self-review-admission` environment, but those controls do not turn the generic
App into a distinct broker identity. Replace it with a dedicated App if an
independent security boundary is required.

## Rejection and invalidation remediation

Read the decision `reason` (and CLI `remediation`) before retrying. Never try to
repair this gate by asking the PR author to submit `APPROVED`; GitHub rejects
that operation and SPipe deliberately claims no provider approval.

| Reason class | Required remediation |
|---|---|
| Push, head/base/merge-base/diff drift, retarget, ruleset or policy change, or expiry | Resolve the current provider state, run a new high-capability review at `high` effort or above with zero P0/P1 on that exact head, then dispatch `SPipe Self Review Admission` again. |
| Matching operator `deny` | Stop. The external policy owner must deliberately replace or expire the exact signed deny record, or the PR must use a separately eligible independent-review route. A caller cannot override it. |
| `constrain` does not cover every path, or a deny scope matches | Reduce/move the change into the allowed scope or ask the external policy owner to issue a new exact constraint. Then review the new exact head and redispatch. |
| Credential/secret semantics, restricted name, traversal, alias, symlink, submodule, unsupported type, or non-UTF-8 path | Remove the unsafe material or object from the PR; rotate any exposed credential; create a clean head; review and redispatch. Do not widen a scope to admit it. |
| Missing, malformed, unauthenticated, stale, or broken-chain policy/evidence | Restore the authenticated external JSONL or exact evidence binding, preserving the hash chain and TTL, then rerun from a fresh provider snapshot. |
| Author/reviewer, model/effort, verdict, or P0/P1 mismatch | Use the exact PR author identity, a high-capability model at `high` effort or above, and an honest exact-head `PASS:0:0`; otherwise use an eligible independent reviewer. |

Every retry creates a new decision. Reusing a stale check, editing provider
approval text, or weakening another protected gate is not remediation.

## Applying the GitHub projection

After the workflow is present on the trusted default branch and the external
policy DB secret is configured, the repository policy owner may run:

```sh
sh scripts/release/github-policy.shs apply-live --yes ormastes/simple
```

Live apply is intentionally limited to the configured `self_attested` generic
Actions mode. Its preflight requires the explicit generic-App trust acceptance,
App ID, zero provider approvals, exact `SPipe Self Review Admission` status
check, read-only repository workflow defaults, and the protected-branch-only
`self-review-admission` execution environment. It then applies only the `main`
and `release/*` self-review rulesets together with those workflow defaults and
environment. An unconfigured `broker_signed` mode fails closed; the dedicated
candidate/release broker remains a separate unsupported lane.

The mutating command must run from a clean checkout whose `HEAD` is the exact
provider-resolved `main` head. It does not derive check names or App IDs from
mutable broker JSON. Instead it generates the complete canonical normalized
`main` and `release/*` rulesets with literal protected-ref conditions,
deletion/non-fast-forward guards, review-thread and create-time enforcement,
merge methods, and the exact `Code Idiom & Structural Ratchet Gates` and
`SPipe Self Review Admission` checks from GitHub Actions App ID 15368. Generated
bytes must match the pinned normalized SHA-256 values and the checked-in
manifests before any API write.

The command finishes by reading the live rulesets, environments, workflow
defaults, and immutable-release setting back from GitHub. PUT payloads and
post-apply comparisons use the same frozen canonical snapshot, so concurrent
local projection drift cannot redefine success. Every normalized projection
must match before it prints the deterministic live projection SHA-256. A digest
is post-apply configuration evidence, not review, candidate, or release
admission. Run `verify-live` separately for read-only inspection.

Immediately before success, the workflow re-resolves the PR/base/ruleset and
regenerates the merge-base diff and compares the normalized active-ruleset
digest. PR edit/retarget/synchronize/close events, protected-base pushes, and
operator policy/ruleset dispatch immediately reset same-head success to
`action_required`. A five-minute scheduled invalidator is the backup and also
resets expired success to `action_required`. The event-driven path depends on
provider delivery and job completion; it is not a claim that GitHub checks are
permanent or race-free. The workflow calls the pure current-decision check
immediately before emission. Candidate admission accepts only the separate
`spipe-review-admission/1` schema, so a self-review decision cannot authorize a
release candidate.

Any later push, secret/credential finding, traversal, symlink, submodule,
unsupported type, non-UTF-8/non-ASCII/quoted path alias, stale evidence, broken hash chain, or
unauthenticated input requires rejection and a new review; do not override the
check with provider approval text.
