# Protected Software Release

This is the semantic source for Simple/Spipe stable, alpha, beta, RC, patch, and hotfix release projections.

## Invariants

1. Start one isolated release session with one `work/release/...` or `work/backport/...` branch and one physical worktree. The main worktree is read-only.
2. Read the product version from `release/version.sdn`; all other version locations are checked projections.
3. Use lowercase numbered prereleases: `X.Y.Z-alpha.N`, `X.Y.Z-beta.N`, or `X.Y.Z-rc.N`.
4. Beta maintenance uses `release/X.Y`. Admit only a caller-selected, reviewed bug-fix commit through `simple release backport-check`; record source SHA, change/work IDs, target line/SHA, adaptation reason, review receipt, result SHA, and renewed evidence.
5. Integrate through the protected CAS authority. Never update `main` or `release/*` directly.
6. Create a new immutable `candidate/vX.Y.Z[-pre.N]/aNNN` for every changed source/policy/support/toolchain input.
7. Build and qualify the exact candidate once. Required failures or fallbacks block admission.
8. Verify with the focused release specs and `bin/simple test test --whole --mode=interpreter`. Release consumes verify evidence and does not repair tests/docs.
9. Promotion verifies the admitted commit and artifact digests, then creates one signed annotated `vX.Y.Z[-pre.N]` tag and pushes exactly that ref. Promotion never rebuilds.
10. Ask before external push/publication. Draft, attach exact admitted assets, verify, then publish immutably.
11. Rollback redeploys an earlier admitted release. Withdrawal preserves tag/assets/history. Corrections receive a new beta, RC, or patch number.

## Beta bug-fix flow

```text
session start at exact release/X.Y
  -> verify one reviewed fix and provenance
  -> apply it only on the private work branch
  -> run focused affected tests on the result revision
  -> submit result through CAS integration
  -> create a new beta candidate attempt
```

Do not automatically discover or cherry-pick “all fixes.” Do not accept feature commits, commit ranges, moving branch names, stale reviews, missing adaptation reasons, or evidence from the pre-backport revision.

## Release commands

Use `simple release version-check`, `beta-prepare`, `backport-check`, `candidate-check`, `promote-check`, and `withdraw-check` to validate each boundary before provider mutation. Use `spipe release-guide` and `spipe release-capabilities` to inspect this plugin’s policy surface.

## External authority

Live ruleset changes, signing, protected pushes, GitHub publication, and registry publication require explicit authority. A local plan PASS is not a live release PASS.
