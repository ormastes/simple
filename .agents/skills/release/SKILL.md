---
name: release
description: Prepare and promote stable or prerelease Simple releases from isolated sessions and immutable admitted candidates.
---

# Protected Simple Release

Use [the software-release guide](../../../doc/07_guide/infra/software_release.md) and `release/version.sdn` as the canonical product-version authority.

## Procedure

1. Require a prior verification `STATUS: PASS`, including one `bin/simple test test --whole --mode=interpreter` result and current SPipe/manual evidence.
2. Start an isolated release session: one `work/release/...` branch, one worktree, exact protected target SHA, and private outputs. Never author in the main worktree.
3. Render/check every declared version projection. New prereleases use lowercase numbered `alpha.N`, `beta.N`, or `rc.N`.
4. For beta maintenance, target `release/X.Y`. Admit only one caller-selected reviewed bug-fix commit at a time with source SHA, change/work IDs, review/check receipts, result SHA, exact stable patch-ID equivalence, and renewed focused evidence. Adapted patches fail closed until a separately reviewed equivalence protocol exists. Never automatically select fixes.
5. Before each candidate attempt, after a bootstrap failure fix, and before release admission, fetch once and compare exact `main` and release-line snapshots read-only. Present reviewed fix proposals; do not automatically choose or apply them.
6. Backport an approved `main` fix or forward-port an approved shared release-first fix on an isolated target-specific work branch before candidate admission. Renew evidence, record a divergence receipt, and let integration authority CAS-update the protected target. Only a `non_fix` release-specific compatibility classification with reason, owner, and expiry may remain release-only.
7. Keep `main` as development trunk; never reset/repoint it to `release/X.Y`, make it track the release line, or merge the whole release line merely to carry a fix.
8. Submit through protected compare-and-swap integration and create a new immutable `candidate/v.../aNNN`.
9. Build and qualify the exact candidate once. Required failures, stale inputs, and fallback artifacts block admission.
10. Promotion verifies exact candidate/artifact/evidence digests and prepares one signed annotated tag pushed as one exact ref. Promotion never rebuilds.
11. Ask before any push or publication. Draft, attach exact assets, verify, then publish immutably.
12. Rollback redeploys an earlier admitted release. Withdrawal preserves tag/assets/history. Corrections receive a new version.

Use `simple release version-check|beta-prepare|backport-check|candidate-check|promote-check|withdraw-check` for the pure validation boundaries.

For protected PR integration, explicitly self-attest high-capability/high-effort PASS with zero P0/P1, then dispatch `SPipe Self Review Admission`. GitHub forbids PR authors from submitting an `APPROVED` review on their own PR; this is a required status check, not provider or independent approval. Ordinary code/text is default allow absent an external operator deny/constrain, using `code`, `text`, exact `file`, immediate `directory_files`, and descendant `directory_recursive` scopes. The trusted default-branch workflow resolves/re-resolves protected target/ruleset, head, base, merge-base, and diff before a ten-minute result. If rejected or invalidated, follow the reason: state drift/expiry needs a fresh exact-head review and dispatch; deny needs policy-owner action or an eligible independent route; uncovered scope needs a smaller diff or new constraint; unsafe/secret material must be removed and any credential rotated. Never use author `APPROVED`, a stale check, or weaker candidate/release/publication authority as remediation. The generic Actions App is not an independent security boundary. Candidate admission accepts only `spipe-review-admission/1`; keep release-environment approval separate.

For `self approve`, `approve PR`, or `author cannot approve`, run `spipe self-review-guide`; this is the canonical exact-head status workflow, not provider `APPROVED`.

For the repository mutation boundary, use
`scripts/release/converge-reviewed-fix.shs` with one exact commit and its bound
`spipe-review-receipt/1`. It fetches both remote heads before creating the
private branch/worktree, emits `spipe-reviewed-fix-preparation/1`, and stops
before push or protected integration.

Never move `main` or `release/*` directly, broadly push every local tag, create unsigned/lightweight release tags, delete or move published tags, rebuild during promotion, or substitute seed/old/source-only artifacts.

Live rulesets, signing, protected pushes, and publication require explicit authority. Do not confuse a local plan PASS with a live release PASS.
