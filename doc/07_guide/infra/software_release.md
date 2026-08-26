# Software Release Guide

This is the operator guide for Simple and Spipe stable, alpha, beta, RC, patch, and hotfix releases. It describes the protected workflow; external mutation still requires the corresponding authority and live server gates.

## Rules

- One mutating session owns one `work/*` branch, one linked worktree/JJ workspace, an exact base/target SHA, and private output/cache directories. Never author in the main worktree.
- `release/version.sdn` is the editable product-version authority. `VERSION`, source identities, and package manifests are projections checked before candidate creation.
- New prereleases are lowercase and numbered: `X.Y.Z-alpha.N`, `X.Y.Z-beta.N`, or `X.Y.Z-rc.N`.
- Protected refs are updated only through integration/release authority. Candidate refs and release tags are create-once.
- Build one exact candidate, qualify it, and promote its artifacts unchanged. Promotion never compiles or packages.
- Published identity is immutable. Rollback redeploys; withdrawal preserves; correction increments.

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

During a long beta or bootstrap qualification run, schedule an occasional read-only fetch-and-compare checkpoint. It reports reviewed bug-fix commits present on only one of `main` or `release/X.Y`; it must not choose, cherry-pick, merge, or push a fix. Avoid tight polling and do not give the bootstrap worker protected-ref credentials.

For each operator-selected exact commit:

1. From `main` to `release/X.Y`, create a private backport branch/worktree, verify the source review, apply only that commit, renew focused evidence, and submit to the release-line integration authority.
2. From `release/X.Y` to `main`, create a private forward-port branch/worktree targeting the exact current `main`, apply or adapt only the reviewed fix, obtain review and renewed evidence, and submit to the trunk integration authority.
3. Record a divergence receipt with both before SHAs, direction, source/result commits, review/evidence/integration digests, deliberately omitted fixes and reasons, and remaining divergence.

If either protected head changes, discard stale admission and retry from a fresh snapshot. `main` always remains the development trunk: never reset or repoint it to `release/X.Y`, make the release branch its upstream, merge an entire maintenance line merely to carry one fix, or push either protected ref directly. Release-only compatibility changes may remain on the release line when the divergence receipt explains why; shared bug fixes must be forward-ported unless explicitly rejected by review.

Required platform rows are declared in `release/support.sdn`. The candidate
workflow `.github/workflows/candidate.yml` builds the exact create-once
candidate ref, runs full bootstrap and whole tests, and emits immutable product,
SBOM, qualification, checksum, provenance-attestation, support, and admission
evidence. The promotion
workflow `.github/workflows/release.yml` accepts only that successful workflow
run, revalidates the candidate ref/commit and every digest, then signs one exact
tag and publishes the unchanged assets. Promotion contains no compiler build or
fallback path.

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

## Withdrawal and rollback

Use `simple release withdraw-check`. Redeployment may select a prior valid release. Do not delete/move a tag, replace assets under the same identity, or reuse a version. Publish an advisory and create a new beta/RC/patch correction.

## Spipe inspection

`spipe release-guide` prints the plugin semantic source. `spipe release-capabilities` reports the session/release/candidate schemas and planning capabilities. These are read-only surfaces; they do not grant protected mutation authority.

## Current blockers to a live release claim

The existing GitHub release workflow remains tag-triggered and contains required-path fallbacks identified in the 2026-08-26 research. Live ruleset parity, signing configuration, promote-only workflow conversion, immutable GitHub release publication, registry digest verification, and the whole-suite result must all be proven before claiming a real beta release PASS.
