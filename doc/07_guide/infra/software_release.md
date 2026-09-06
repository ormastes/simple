# Software Release Guide

This is the operator guide for Simple and Spipe stable, alpha, beta, RC, patch, and hotfix releases. It describes the protected workflow; external mutation still requires the corresponding authority and live server gates.

## Rules

- One isolated mutating session owns one `work/*` branch, one linked worktree/JJ workspace, an exact base/target SHA, and private output/cache directories. Never author in the main worktree.
- `release/version.sdn` is the editable product-version authority. `VERSION`, source identities, and package manifests are projections checked before candidate creation.
- New prereleases are lowercase and numbered: `X.Y.Z-alpha.N`, `X.Y.Z-beta.N`, or `X.Y.Z-rc.N`.
- Protected refs are updated only through integration/release authority. Candidate refs and release tags are create-once.
- Build one exact candidate, qualify it, and promote its artifacts unchanged. Promotion never compiles or packages.
- Published identity is immutable. Rollback redeploys; withdrawal preserves; correction increments.

## Session registration

Before any repository-backed release mutation, the trusted session authority
canonicalizes the repository root, verifies that it is a linked non-main Git
worktree, checks the checked-out `work/*` branch and exact `HEAD`, refreshes the
declared target identity, and verifies the VCS-policy digest. It then registers
the session under a repository-wide lock. Session ID, canonical workspace, and
work branch each have one active owner, and the session receives private
`build/session/<id>/output` and `cache-overlay` namespaces. A conflicting,
malformed, symlink-aliased, detached, stale, or unregistered session fails
closed.

## Beta release and bug fixes

Create/use `release/X.Y` at the protected target. Start `work/release/vX.Y.Z-beta.N-<session>`. A beta may incorporate a bug fix only when an operator supplies one exact reviewed source commit.

Validate each fix with `simple release backport-check` and record:

- exact source commit;
- stable change and work IDs;
- `kind=fix`;
- review receipt digest;
- `release/X.Y` and expected target SHA;
- exact stable patch ID (`adapted` is not admitted by this protocol);
- post-application result SHA;
- renewed focused evidence digest for that result.

Apply the commit only on the private work branch, rerun affected tests, and submit by compare-and-swap. Feature commits, ranges, moving branch names, automatic “all fixes” selection, stale review, or pre-application evidence are rejected. Every changed input creates a new candidate attempt and, after publication, a new beta number.

### Periodic main/release convergence

During a long beta or bootstrap qualification run, schedule a bounded read-only fetch-and-compare checkpoint before every candidate attempt, after a bootstrap failure is repaired, and before release admission. `inspect_release_main_convergence` fetches exact remote heads with bounded refspecs, compares at most 256 source-only commits, and verifies that every selected SHA is review-bound, reachable from the source, and not already represented in the target. It must not choose, cherry-pick, merge, or push a fix. Avoid tight polling and do not give the bootstrap worker protected-ref credentials.

The default-branch workflow `release-convergence-checkpoint.yml` invokes a
source-hosted observation every six hours and by operator dispatch. Scheduled runs derive
`release/X.Y` from `release/version.sdn` and report not-applicable when that
line does not exist; an operator dispatch requires the line to exist and may
name it explicitly. It fetches only the two exact remote-tracking refs, bounds
each source-only inventory to 256 commits, and emits
`simple-release-source-convergence-observation/1` JSON. It invokes no compiler
at all: `deployed_runtime_used=false` and `release_admission_eligible=false`
make the fresh-runner boundary explicit instead of pretending that source-hosted
Git comparison is a deployed pure-Simple payload.
The equivalent local observation is:

```sh
scripts/release/convergence-checkpoint.shs --release-ref=release/X.Y --require-release-line
```

A checkpoint is an operator hint only: it cannot
select a fix or satisfy review, backport/forward-port, integration, candidate,
or promotion admission.

For each operator-selected exact commit:

1. From `main` to `release/X.Y`, create a private backport branch/worktree, verify the source review, apply only that commit, renew focused evidence, and submit to the release-line integration authority.
2. From `release/X.Y` to `main`, create a private forward-port branch/worktree targeting the exact current `main`, apply the exact patch-equivalent reviewed fix, obtain review and renewed evidence, and submit to the trunk integration authority. An adapted patch fails closed until a separate equivalence protocol is reviewed and implemented.
3. After protected CAS integration, `record_post_integration_divergence` fetches
   both heads again. It requires an unchanged source, an append-only target equal
   to the reviewed result, representation of every selected patch, and exact
   review/evidence/integration digests. For a forward port, it also proves the
   release source head is not an ancestor of the resulting `main`, rejecting a
   whole-line merge even when the heads differ.

If either protected head changes, discard stale admission and retry from a fresh snapshot. The reviewed manifest binds the exact current `main_head_sha`; a main advance after review requires a new reviewed integration. `main` always remains the append-only development trunk: never repoint it to `release/X.Y`, make the release branch its upstream, merge or otherwise absorb an entire maintenance line, or push either protected ref directly. The release line likewise must not absorb the whole current `main`; both ancestry directions fail closed. Before candidate admission, the reviewed manifest names an exact `release_inventory_head_sha`. That boundary must extend the integration base, be an ancestor of the reviewed PR head, and be followed only by manifest-only administrative commits, so the inventory never requires a commit to contain its own SHA. Recompute the complete release-only inventory at that boundary and require one receipt-bound `fix` or `non_fix` classification for every commit; a nonempty inventory cannot be paired with an empty classification list. Every selected `main` fix must name a result reachable in the pre-merge release inventory, match it by exact `git patch-id --stable`, and carry the exact release integration review/check receipt. Every release-first `fix` classification must symmetrically name a result represented on `main`, match the same stable patch ID, and carry an exact main-targeted forward-port receipt. Candidate CI replays both source-to-result bindings. Adapted fixes require a future separately reviewed equivalence path and are not admitted by this one. Bug fixes have no waiver. Genuinely release-specific compatibility work may remain release-only only under a distinct non-fix classification with a nonempty reason, accountable owner, and unexpired RFC 3339 expiry.

Provider evidence accepts only configured required check identities: exact check name, GitHub App integration ID, exact PR head, completed state, and `success` conclusion. Neutral, skipped, unrelated, duplicate, or name-only check runs do not satisfy release admission. The canonical check identities are projected together in `.spipe/policy/vcs.sdn` and the protected branch rulesets.

### Protected PR scoped self-review admission

Protected `main`, `integration/main`, and `release/*` PRs require zero provider
Approve reviews. Instead, their rulesets require both `Code Idiom & Structural
Ratchet Gates` and `SPipe Self Review Admission` from the GitHub Actions App
identity. The latter is an exact-head check, not an Approve review and not a
claim that GitHub accepted self-approval.

GitHub forbids a PR author from submitting an `APPROVED` review on their own
PR. The required SPipe status is the deliberate provider-compatible mechanism:
it records a scoped, short-lived admission without fabricating provider or
independent approval. Ordinary code/text is eligible by default only when the
authenticated external policy is valid and no matching deny/constrain narrows
it. Exact scopes are `code`, `text`, `file`, `directory_files` (immediate files),
and `directory_recursive` (descendants).

After self-review with a high-capability model at `high` effort or above, Spipe
dispatches PR number, the reviewed `expected_head_sha`, session, model/effort,
and literal `PASS:0:0`. This is
explicit `self_attested` evidence, not an authenticated higher-model receipt or
independent review. The expected head is only a review binding: the workflow
independently resolves the live provider head and rejects any mismatch. It
accepts no caller base/diff/ruleset. From its trusted default-branch definition
it resolves protected target/ref/ruleset, author, base, merge-base, and changed paths, then re-resolves them before
publishing a ten-minute `spipe-self-review-decision/1` check. Push, retarget,
ruleset change, diff drift, or expiry requires a new dispatch.

On rejection or invalidation, read the reported reason before retrying. State
drift or expiry requires a fresh exact-head high-effort review with zero P0/P1
and a new dispatch. A matching deny requires external policy-owner action or an
eligible independent-review route. An uncovered constraint requires reducing
the diff or a new external constraint. Secret/credential, traversal, alias,
symlink, submodule, unsupported-type, or encoding rejection requires removing
the unsafe material (and rotating any exposed credential) before creating and
reviewing a new head. Missing/malformed policy or evidence must be restored at
its external authority. Never remediate by attempting author `APPROVED`,
reusing a stale check, or weakening candidate/release/publication controls.

The checked-in `.spipe/policy/self-review-policy.sdn` is projection only and
cannot grant or deny a session. Operator policy is external UTF-8 JSONL from
the `SPIPE_SELF_REVIEW_POLICY_DB` Actions secret with schema
`spipe-self-review-policy-db/1`; a missing, malformed, unauthenticated, broken
hash chain, or over-24-hour record fails closed. Ordinary code and text is
allowed by default. An exact matching `deny` record rejects the user/session;
each exact matching `constrain` record must cover every path and any deny scope
wins. Scope kinds are `code`, `text`, exact `file`, immediate
`directory_files`, and descendant `directory_recursive`. Rename evaluates old
and new names, delete the old name, and copy the new name. Traversal, symlink,
submodule, unsupported type, non-UTF-8, noncanonical classification, and
authenticated credential/secret material are denied. Unknown extensions count
as code. Policy, workflow, guide, and evaluator source text remains reviewable.

`simple release self-review-plan` is the pure decision boundary. It reads the
policy only from the path named by `SPIPE_SELF_REVIEW_POLICY_DB`, consumes the
server-generated target/head/base/merge-base/diff manifest, emits no mutation,
and always reports `provider_approval_claimed=false`. The current user policy
uses explicit `self_attested` review evidence. It must never be labeled as an
authenticated higher-model receipt or independent approval. Release-candidate
admission and protected release/npm environments are separate authorities and
retain their independent controls. The exact external JSONL header, record,
scope, hash-chain, evidence, and audit formats are documented in
`doc/07_guide/infra/self_review_policy_db.md`.

The check is short lived: the workflow binds a canonical digest of the active
ruleset, re-resolves the target/ref/ruleset digest, regenerates the exact
merge-base diff, and reruns the pure current-decision consumer immediately
before success. Trusted `pull_request_target` events immediately reset a
same-head success to `action_required` after synchronize, edit/retarget,
reopen, or close; protected-base pushes do the same for base-SHA movement, and
operator policy/ruleset changes use repository dispatch. The five-minute
schedule is only a backup for expiry or missed delivery. Strict up-to-date
remains mandatory.

Direct GitHub merge cannot call the pure Simple consumer after the check has
completed. Its provider gate is therefore the exact-head required check plus
the event invalidators and strict ruleset. Candidate admission separately
accepts only `spipe-review-admission/1`; a `spipe-self-review-decision/1`, stale
or current, cannot authorize release. GitHub cannot make a success permanent
authority, and this design does not claim that it can.

By explicit user decision, the ruleset currently trusts generic GitHub Actions
App ID 15368. Repository Actions defaults are read-only and the intended
default-branch emitter uses the `self-review-admission` environment, but a
same-repository PR workflow can still potentially spoof that generic context.
This is an accepted trust risk, not an independent broker security boundary.
The `pull_request_target` invalidator uses only the protected default-branch
workflow definition and provider payload/API data; it never checks out or
executes pull-request code. Event delivery and the same generic Actions App
identity remain part of the explicitly accepted residual risk. "Immediate"
means event-driven rather than waiting for the schedule: GitHub does not
guarantee event-job completion before every concurrent merge attempt, so this
workflow does not claim an impossible permanent or race-free approval.

#### One-time bootstrap plan

The workflow/evaluator cannot protect the merge that first installs them. For
that one transition only, freeze repository mutation, record the exact current
ruleset IDs/digests and PR head, obtain an xhigh exact-head PASS with zero
P0/P1, configure the external default-allow JSONL header secret, and have the
repository policy owner temporarily set approval count to zero while retaining
the existing structural check. Merge only the recorded PR head, verify the new
default-branch workflow/evaluator bytes, immediately CAS-apply the final
rulesets requiring `SPipe Self Review Admission`, and verify live projection
parity. Abort and restore the captured rulesets if the protected head, PR head,
review receipt, policy digest, or any intervening PR changes. Retain before,
transition, merge, and final-policy receipts. This is a one-use migration plan,
not a reusable bypass or release approval.

### Candidate/release independent review and sole-owner fallback

Normal admission uses a closed `spipe-review-admission/1` receipt from a
high-capability model running at `high` effort or above. The receipt binds the
repository, PR number, feature/session identifier, server-resolved current head
SHA, exact required check identities, PASS verdict, review/audit digests, issue
time, and an expiry no more than 24 hours later. A later push changes the current
head and invalidates the receipt and status.

Only when that verifier mechanism is unavailable may the repository owner
explicitly dispatch `authority_class=owner_attested_actions` from trusted
`main`, with `NO-VERIFY:OWNER-PROOF`. The dedicated
`owner-convergence-admission` environment requires owner ID `2378857` and has
`prevent_self_review=false`; protected-integration, release, and npm-release
remain unchanged. The eight-hour receipt is sized for queueing plus the full
Stage 2/3/4 candidate qualification, says `verification_performed=false` and
`github_pr_approval_claimed=false`, retains the verifier-unavailability proof,
and binds the exact run, workflow source commit/blob, live policy, rulesets,
environment, PR/parents, candidate, manifest, forward ports, and required
checks. Candidate admission fetches the exact run/artifact/digest and verifies
its GitHub attestation with `--signer-workflow`, signer digest, source ref, and
self-hosted runners denied; it separately inspects the authenticated certificate
identity fields because `--signer-workflow` and `--cert-identity` are mutually
exclusive GitHub CLI selectors. Immediately before the pure admission decision,
the candidate re-resolves live main, release, and candidate refs, revalidates
the environment/ruleset/config projection and trusted workflow, and rechecks
expiry. The longer queue allowance therefore does not survive any protected
state drift. Candidate content is fetched as data and never executed. Same
author/merger is accepted only in this fallback; normal external broker
admission retains the inequality. This is not an admin bypass, self-review, or
permission to omit checks.

Forward-port receipt replay branches on the convergence authority before any
broker lookup. External mode retains the exact broker App admission check.
Owner mode accepts both empty and non-empty forward-port sets only when every
row carries `authority_class=owner_attested_actions`, false verification and
GitHub-approval claims, null broker identity, and the exact configured required
checks for the recorded PR head.

This candidate/release receipt is distinct from PR `SPipe Self Review
Admission`. GitHub rulesets cannot natively express conditional model review
versus owner attestation, and environment required reviewers cannot represent
that alternative. Therefore the `SPipe Review Admission` App/custom-environment
portion of `.github/review-admission-broker.json` remains the preferred route
when its external signed protocol and dedicated App are configured. The owner
fallback must prove that route unavailable and fails closed otherwise.

Prepare one selected fix with `scripts/release/converge-reviewed-fix.shs`. The
command requires a create-once `spipe-review-receipt/1` file bound to the exact
approved commit, change ID, and `kind=fix`; the command snapshots and hashes
those bytes before fetching. It first fetches bounded source and target refs from the configured
remote, then creates one unique `work/backport/*` or `work/forwardport/*`
branch and linked worktree at the fetched target SHA. A conflict removes the
new private worktree/branch and fails closed. Success emits a
`spipe-reviewed-fix-preparation/1` receipt under the session-private build
tree and leaves the branch for renewed tests, PR review, and protected CAS
integration. It never pushes or moves `main` or `release/*`.

Required platform rows are declared in `release/support.sdn`. The candidate
workflow `.github/workflows/candidate.yml` builds the exact create-once
candidate ref, runs full bootstrap and whole tests, and emits immutable product,
SBOM, qualification, checksum, provenance-attestation, support, convergence,
and admission evidence. It also packs the MCP and LSP MCP npm tarballs from the
candidate workspace and admits their exact bytes. The canonical schemas are
`simple-release-candidate/1`, `simple-release-qualification/1`, and
`simple-release-admission/1`; the admission binds the candidate identity and
all source, policy, version, toolchain, support, build-graph, creator, evidence,
qualification, convergence, and artifact identities. The promotion
workflow `.github/workflows/release.yml` accepts only that successful workflow
run, revalidates the candidate ref/commit and every digest, then signs one exact
tag and publishes the unchanged assets. A retry accepts only the already-signed
tag with the same commit/admission digest, resumes an existing draft, compares
already-uploaded asset bytes, rejects extra or missing assets, and verifies the
published immutable release. Promotion contains no compiler build, package,
version rewrite, or fallback path.

Support policy uses three explicit tiers. Tier 1 rows are release promises;
every row marked `required: true` needs a full-bootstrap and whole-test receipt.
Tier 2 rows remain visible even when they are not channel-blocking. Experimental
rows never silently become required. Each row records `supported`, `blocked`,
or `experimental` availability, and the candidate receipt records `passed`,
`not_executed`, `unsupported`, `experimental`, or `blocked`. Only actually
executed required rows may say `passed`; a missing required receipt blocks
admission. The current beta contract requires Linux x86_64 and reports the
macOS/Windows Tier 2, blocked FreeBSD, and experimental ARM/RISC-V rows without
claiming they passed. RC and stable declare the broader native desktop Tier 1
matrix and therefore fail closed until candidate CI aggregates those platform
receipts. No lane may substitute a seed, source-only, or foreign-target fallback
artifact for a missing native result.

## Candidate

Run `simple release candidate-check` over the canonical version, positive attempt, `candidate/v.../aNNN`, exact commit, and source/policy/version/toolchain/support/evidence digests. Existing identical identity is idempotent; a different identity at the same candidate is mutation and fails.

Builders consume that immutable candidate. Required target failure, unsupported fallback, seed/old binary substitution, source-only replacement, or missing evidence blocks admission.

## Promotion

After `$verify` reports `STATUS: PASS`, including one `bin/simple test test --whole --mode=interpreter` run, use `simple release promote-check`. It requires:

- an admitted candidate identity and exact commit;
- exact matching artifact/evidence manifests;
- canonical `vX.Y.Z[-pre.N]` tag;
- signed and annotated tag intent;
- exact single-ref push intent;
- no rebuild and no fallback.

Ask before external push or publication. A release authority signs the exact admitted commit, pushes that one tag, creates a draft, attaches exact admitted assets, verifies digests, and then publishes immutably. The local checker does not itself sign, push, change rulesets, or publish.

The release-published npm workflow downloads the admitted `.tgz` assets,
verifies their checksum and immutable-release attestation, and publishes the
tarballs themselves with `alpha`, `beta`, `rc`, or `latest` distribution tags.
If a package version already exists, it is accepted only when the registry
tarball is byte-identical and its distribution tag already points to that
version; otherwise the retry fails.

## Withdrawal and rollback

Use `simple release withdraw-check`. Redeployment may select a prior valid release. Do not delete/move a tag, replace assets under the same identity, or reuse a version. Publish an advisory and create a new beta/RC/patch correction.

## Spipe inspection

`spipe release-guide` prints the plugin semantic source. `spipe release-capabilities` reports the session/release/candidate schemas and planning capabilities. These are read-only surfaces; they do not grant protected mutation authority.

## Current verification boundary

The prior live GitHub configuration baseline covered all seven declared
rulesets, the protected-integration, release, and npm-release environments, and
immutable releases. The complete privileged self-review projection additionally
requires read-only repository Actions defaults and the declared
`self-review-admission` environment; `verify-live` now checks those surfaces and
prints a normalized projection SHA-256 only after every comparison passes. This
is configuration evidence, not release admission.
The declared environment reviewer is also the sole repository owner, so GitHub
`prevent_self_review` still makes the release-environment path circular. The
candidate/release `SPipe Review Admission` App projection is not configured and
its future `broker_signed` lane remains fail-closed. `github-policy.shs
apply-live --yes` supports only the separately configured, explicitly
user-accepted `self_attested` generic-Actions lane: it sets read-only workflow
defaults, declares the `self-review-admission` environment, applies the `main`
and `release/*` rulesets with zero provider approvals and exact `SPipe Self
Review Admission`, then runs live parity verification and emits its digest. The
source projection is not live evidence until the repository policy owner runs
that command after configuring the external policy DB secret and retains its
post-apply receipt.

The exact release lineage still lacks admitted Stage 3 and Stage 4 receipts and
one clean release-grade `bin/simple test test --whole --mode=interpreter` PASS.
No signed beta tag, immutable candidate publication, or byte-identical npm
publication receipt exists. Those rows remain FAIL and must not be inferred
from the live policy PASS or from workflow source.
