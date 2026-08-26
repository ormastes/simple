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
4. For beta maintenance, target `release/X.Y`. Admit only one caller-selected reviewed bug-fix commit at a time with source SHA, change/work IDs, review receipt, adaptation reason, result SHA, and renewed focused evidence. Never automatically select fixes.
5. At bounded beta/bootstrap checkpoints, fetch once and compare exact `main` and release-line snapshots read-only. Present reviewed fix proposals; do not automatically choose or apply them.
6. Backport an approved `main` fix or forward-port an approved release-first fix on an isolated target-specific work branch. Renew evidence, record a divergence receipt, and let integration authority CAS-update the protected target.
7. Keep `main` as development trunk; never reset/repoint it to `release/X.Y`, make it track the release line, or merge the whole release line merely to carry a fix.
8. Submit through protected compare-and-swap integration and create a new immutable `candidate/v.../aNNN`.
9. Build and qualify the exact candidate once. Required failures, stale inputs, and fallback artifacts block admission.
10. Promotion verifies exact candidate/artifact/evidence digests and prepares one signed annotated tag pushed as one exact ref. Promotion never rebuilds.
11. Ask before any push or publication. Draft, attach exact assets, verify, then publish immutably.
12. Rollback redeploys an earlier admitted release. Withdrawal preserves tag/assets/history. Corrections receive a new version.

Use `simple release version-check|beta-prepare|backport-check|candidate-check|promote-check|withdraw-check` for the pure validation boundaries.

Never move `main` or `release/*` directly, broadly push every local tag, create unsigned/lightweight release tags, delete or move published tags, rebuild during promotion, or substitute seed/old/source-only artifacts.

Live rulesets, signing, protected pushes, and publication require explicit authority. Do not confuse a local plan PASS with a live release PASS.
