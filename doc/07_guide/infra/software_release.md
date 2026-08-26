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
- adaptation reason (`none` is explicit);
- post-application result SHA;
- renewed focused evidence digest for that result.

Apply the commit only on the private work branch, rerun affected tests, and submit by compare-and-swap. Feature commits, ranges, moving branch names, automatic “all fixes” selection, stale review, or pre-application evidence are rejected. Every changed input creates a new candidate attempt and, after publication, a new beta number.

### Periodic main/release convergence

During a long beta or bootstrap qualification run, schedule an occasional read-only fetch-and-compare checkpoint. `inspect_release_main_convergence` fetches exact remote heads with bounded refspecs, compares at most 256 source-only commits, and verifies that every selected SHA is review-bound, reachable from the source, and not already represented in the target. It must not choose, cherry-pick, merge, or push a fix. Avoid tight polling and do not give the bootstrap worker protected-ref credentials.

For each operator-selected exact commit:

1. From `main` to `release/X.Y`, create a private backport branch/worktree, verify the source review, apply only that commit, renew focused evidence, and submit to the release-line integration authority.
2. From `release/X.Y` to `main`, create a private forward-port branch/worktree targeting the exact current `main`, apply or adapt only the reviewed fix, obtain review and renewed evidence, and submit to the trunk integration authority.
3. After protected CAS integration, `record_post_integration_divergence` fetches
   both heads again. It requires an unchanged source, an append-only target equal
   to the reviewed result, representation of every selected patch, and exact
   review/evidence/integration digests. The receipt proves that `main` and the
   maintenance line remain distinct.

If either protected head changes, discard stale admission and retry from a fresh snapshot. `main` always remains the development trunk: never reset or repoint it to `release/X.Y`, make the release branch its upstream, merge an entire maintenance line merely to carry one fix, or push either protected ref directly. Release-only compatibility changes may remain on the release line when the divergence receipt explains why; shared bug fixes must be forward-ported unless explicitly rejected by review.

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

The repository now contains candidate-build, promote-only release, and
admitted-tarball publication workflows, but their presence is not evidence that
GitHub rulesets, signing, immutable-release settings, environments, or registry
publication are configured and working live. The available local `simple`
runtime identifies itself as bootstrap seed-derived, so it cannot supply the
required release-grade whole-suite evidence. The trusted-session integration
spec also exceeded its bounded test timeout in the final verification pass.
Both facts remain release blockers until fresh admitted-runtime and bounded
session evidence pass; neither may be converted to a warning or inferred PASS.
