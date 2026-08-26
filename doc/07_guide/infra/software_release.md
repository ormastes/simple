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

Prepare one selected fix with `scripts/release/converge-reviewed-fix.sh`. The
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

The live GitHub configuration baseline passes
`scripts/release/github-policy.sh verify-live ormastes/simple`: all seven
declared rulesets match their projections, the protected-integration, release,
and npm-release environments exist with the declared policy, and immutable
releases are enabled. This is configuration evidence, not release admission.

The exact release lineage still lacks admitted Stage 3 and Stage 4 receipts and
one clean release-grade `bin/simple test test --whole --mode=interpreter` PASS.
No signed beta tag, immutable candidate publication, or byte-identical npm
publication receipt exists. Those rows remain FAIL and must not be inferred
from the live policy PASS or from workflow source.
