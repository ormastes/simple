<!-- llm-process-gen: managed source=pipe_release_skill source_sha256=8101a3f942cf7248127ec5931807a5fd55425fb7bfb11ea1aedfaa70a7a6551b content_sha256=861814efcb71cb4d3344e56009aaefefe93af4452886d06d8ca671c9faff85da -->
# Release Skill

Release contract: isolated-session; reviewed-beta-backport; immutable-candidate; promote-without-rebuild; protected-ref-guard; non-destructive-release-identity.

## Usage

```
/release              # patch bump (default): 0.9.2 → 0.9.3
/release patch        # same as above
/release third        # same as above
/release minor        # minor bump: 0.9.2 → 0.10.0
/release second       # same as above
/release major        # major bump: 0.9.2 → 1.0.0
/release first        # same as above
/release 1.0.0        # set exact version
```

## Procedure

Given argument: `$ARGUMENTS`

- One isolated release session owns one work branch and one non-main worktree.
- `release/version.sdn` is the sole version authority and all other version locations are checked projections.
- Beta maintenance admits only caller-selected reviewed bug-fix commits with exact provenance and renewed result-revision evidence.
- Bootstrap periodically performs read-only main-to-release convergence discovery and never selects or cherry-picks fixes automatically.
- An approved release-first emergency fix requires an exact reviewed forward-port receipt to main.
- Main remains the independent development trunk and never tracks or becomes a release branch.
- Protected refs change only through exact-revision compare-and-swap integration authority.
- Each changed source policy support or toolchain identity creates a new immutable candidate attempt.
- Build and qualify the exact candidate once and reject required failures or fallback artifacts.
- Promotion reuses admitted artifacts without rebuilding and pushes exactly one signed annotated tag.
- Release admission requires focused failures to reach zero followed by one clean whole-suite confirmation.
- Withdrawal preserves published tags assets and history and corrections use a new version.
- Protected PR self review uses a required status check because GitHub forbids an author APPROVED review and never claims provider approval.
- Ordinary code and text are eligible by default absent an operator deny or constrain record with code, text, file, directory_files, and directory_recursive scopes.
- Push, retarget, base, diff, ruleset, policy, or expiry invalidation requires a fresh exact-head review and a new self-review admission dispatch.
- Rejection remediation follows the exact reason without broadening protected integration, candidate, release, signing, or publication authority.
