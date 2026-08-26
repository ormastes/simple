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
5. Submit through protected compare-and-swap integration and create a new immutable `candidate/v.../aNNN`.
6. Build and qualify the exact candidate once. Required failures, stale inputs, and fallback artifacts block admission.
7. Promotion verifies exact candidate/artifact/evidence digests and prepares one signed annotated tag pushed as one exact ref. Promotion never rebuilds.
8. Ask before any push or publication. Draft, attach exact assets, verify, then publish immutably.
9. Rollback redeploys an earlier admitted release. Withdrawal preserves tag/assets/history. Corrections receive a new version.

Use `simple release version-check|beta-prepare|backport-check|candidate-check|promote-check|withdraw-check` for the pure validation boundaries.

Never move `main` or `release/*` directly, use `git push --tags`, create unsigned/lightweight release tags, delete or move published tags, rebuild during promotion, or substitute seed/old/source-only artifacts.

Live rulesets, signing, protected pushes, and publication require explicit authority. Do not confuse a local plan PASS with a live release PASS.

