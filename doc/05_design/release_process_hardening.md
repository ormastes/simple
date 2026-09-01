<!-- codex-design -->

# Release Process Hardening Detailed Design

## Module contracts

### Version policy

`parse_release_version(text)` recognizes stable and numbered lowercase prerelease versions. `validate_version_channel(version, channel)` rejects suffix/channel mismatch. `check_version_projection(expected, name, observed)` returns a stable drift reason. Rendering uses `ReleaseVersion.canonical()`.

### Session policy

`ReleaseSession` contains session ID, workspace path, main-worktree path, work branch, target ref, base SHA, expected target SHA, and policy hash. `validate_release_session` rejects empty identities, equal workspace/main paths, non-`work/` authoring refs, direct protected targets, and missing exact hashes.

`verify_release_session` checks those claims against canonical Git state.
`register_release_session` serializes ownership through a repository-wide locked
registry and rejects duplicate session, workspace, or branch ownership.
`verify_registered_release_session` is the mutation precondition. Private
output and writable cache-overlay paths are derived from the registered session.

### Backport admission

`BackportRequest` fields:

```text
source_commit_sha
change_id
work_id
change_kind
review_receipt_sha256
target_line
expected_target_sha
adaptation_reason
evidence_sha256
result_commit_sha
```

`check_backport_admission` accepts only `change_kind=fix`, `target_line=release/X.Y`, exact nonempty commit/digest facts, and evidence bound after application. Empty adaptation reason is normalized to `none`; ambiguous refs and feature changes reject.

### Convergence discovery and forward-port

`ConvergenceRequest` records exact fetched `main` and `release/X.Y` SHAs, policy digest, discovery timestamp/cadence identity, reviewed fix metadata, and explicit caller selection. `inspect_release_main_convergence` performs bounded Git fetch/ref/ancestry/patch-equivalence checks and returns a fetch-only observation; it cannot apply or push. Each proposal names one exact commit and direction (`main_to_release` or `release_to_main`).

`PostIntegrationDivergenceReceipt` records direction, exact before/after heads,
selected commits, result SHA, and review, renewed-evidence, and integration
digests. It is emitted only after a fresh fetch proves the source unchanged,
the target append-only and equal to the result, and every selected patch present.
For `release_to_main`, the target is always `main`, but application occurs on an
isolated `work/fix/...` or `work/backport/...` branch. Only integration authority
may CAS-update `main`.

Protected admission reads `release_inventory_head_sha` from the reviewed
manifest, requires it between the integration base and head, and permits only
manifest-only commits afterward. It classifies the inventory at that boundary,
requires reason/owner/future-expiry metadata for `non_fix`, and derives exact
provider receipts. Every selected main fix names one result in the pre-merge
release inventory with the same stable patch ID and the release integration
review/check receipt. A release-first `fix` likewise names one reviewed result
on `main` with the same stable patch ID. Configured required checks must match
both check name and GitHub App integration ID with a completed `success` result.

### Candidate

`CandidateManifest` includes canonical version, attempt, ref, commit,
source/policy/version/toolchain/support/build-graph/evidence digests, and creator
identity. `candidate_identity()` returns its SHA-256 canonical identity.
`QualificationReceipt` adds exact artifact, required-support, evidence, and
build-graph identities. CI serializes these as the
`simple-release-candidate/1`, `simple-release-qualification/1`, and
`simple-release-admission/1` schemas; admission carries the same bound fields
plus the qualification and convergence receipt digests.

### Scoped self-review

`SelfReviewPolicyDb` parses external UTF-8 JSONL with one closed
`spipe-self-review-policy-db/1` header followed by closed
`spipe-self-review-policy-db/grant/1` records. Records are `deny` or `constrain`,
use an append hash chain, bind an operator signature/key ID and exact provider,
PR, protected target/ruleset, head, base, merge-base, diff, session, reviewer,
evidence mode/digest, and expiry facts. The checked-in
SDN projection contains no records.

`SelfReviewChangedManifest` binds provider repository numeric/node/name
identity, PR, head, base, merge-base, diff, and every typed path change.
`SelfReviewRequest` additionally binds target ruleset, author/reviewer identity,
explicit self-attestation or genuinely broker-signed evidence, policy DB digest,
and decision expiry. `evaluate_self_review` first rejects
invalid/authentication/stale/secret path facts, then applies exact operator deny
precedence and constraint intersection, finally returning
`spipe-self-review-decision/1`. An allowed decision names a separate check-run
broker action and always sets `provider_approval_claimed=false`.

### Promotion

`ReleaseAdmission` binds the complete candidate identity, qualification receipt,
commit, artifact/evidence manifests, and admitted flag. `PromotionPlan` includes
exact tag, commit, signed/annotated flags, exact-push flag, rebuild flag,
fallback flag, and artifact digest. Provider retries verify an existing signed
tag and remote assets rather than recreating or overwriting them. Candidate CI
packs npm tarballs; publish CI only verifies and publishes those admitted bytes.

`withdrawal_plan(version, redeploy_version, delete_tag, move_tag, reuse_version)` rejects destructive identity changes and otherwise returns an auditable non-mutating plan.

## CLI

The `simple release` surface provides:

```text
version-check --root=...
version-render-plan --root=... --version=... --channel=...
version-bump-plan --root=... --version=... --channel=... <compatibility counters>
version-bump --root=... --manifest-sha256=... <session facts> <compatibility counters>
session-register|session-status|session-cleanup-check|session-close <session facts>
beta-prepare --version=... --target=release/X.Y --target-sha=... --session=...
backport-check --source-sha=... --change-id=... --work-id=... --kind=fix ...
convergence-discover --root=... <session and reviewed selection facts>
convergence-receipt --root=... <post-integration receipt facts>
self-review-plan --policy-db=... --changed-manifest=... <exact target/base/diff/evidence facts>
candidate-check --version=... --attempt=N --commit=... <digest flags>
support-check --root=...
promote-check --tag=v... --commit=... --candidate-commit=... --signed --annotated --exact-push --no-rebuild --no-fallback
withdraw-check --version=... --redeploy=...
```

`support-check` reads `simple-release-support/2`, separates channel-required
rows from the complete declared matrix, and emits both arrays. A candidate job
may mark only its observed target `passed`; non-required supported rows are
`not_executed`, unavailable rows are `unsupported`, and experimental rows stay
`experimental`. If one job cannot account for every required target, the
command fails rather than emitting a partial PASS. The support receipt itself is
checksummed into the candidate evidence and artifact manifest.

Human output is concise. `--json` uses stable status/reason keys. Version apply,
session registration, and convergence observation are repository-backed guarded
operations. They use argv-only Git/process and filesystem facades; they do not
push protected refs, sign, build, or publish. Candidate promotion remains an
approval-gated workflow authority.

## Policy schema changes

Upgrade `.spipe/policy/vcs.sdn` to `spipe-vcs/3`: mandatory unique branch/workspace session authoring; rebase matrix; create-once candidate; exact tag push; immutable signed annotated tags; release/backport authorities; drift fingerprint. Add `release/policy.sdn`, `release/support.sdn`, and `release/legacy-tags.sdn` only when their parsers/checkers are implemented; do not add declarative files that no shipped command reads.

## Spipe plugin

The plugin manifest and JSON/package/protocol identities move together to `0.2.0`. Capabilities and schema declarations are mirrored. Add canonical general software-release guidance and project it into all model surfaces. Extend `scripts/build.shs` with bounded checks for version parity and forbidden unsafe phrases/commands. Initial CLI/MCP release operations expose policy/status/plan documents; mutation waits for a capability-bound provider.

## System scenarios

The executable scenario uses the frozen manual steps:

1. `Load the canonical release policy`
2. `Prepare an isolated beta release`
3. `Admit reviewed bug-fix backports`
4. `Reconcile reviewed fixes with main`
5. `Freeze and qualify the release candidate`
6. `Promote exact admitted artifacts`
7. `Withdraw without rewriting release identity`

Each primary step has success and adjacent rejection assertions. Advanced projection/plugin parity detail is folded. The manual shows commands, expected typed reasons, and recovery behavior without raw test code dominating.

## Migration

1. Land pure types/checkers and focused specs.
2. Route CLI plan/check commands to them.
3. Remove unsafe tag/direct-main text from legacy `prepare.spl` and skills.
4. Update plugin version/capabilities/projections/parity gate.
5. Build and attest candidates in candidate CI, promote only their admitted
   assets in release CI, and publish admitted npm tarballs unchanged.
6. Bootstrap scoped self-review once under a frozen exact-state self-attestation,
   then require its final GitHub Actions check in both protected branch rulesets.

## Runtime boundary decision

`runtime_need: none` for this implementation slice. `facade_checked`: existing release GitHub/process owners were inspected. `chosen_path: reuse-facade` for future execution, while current work remains pure planning. `rejected_shortcuts`: direct `rt_*`, raw Git subprocesses, main-worktree mutations, fixture-only success branches, and provider field pokes.
