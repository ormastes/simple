<!-- llm-process-gen: managed source=gemini_release_skill source_sha256=cba19ebd846a836863e557a9733f55fa347693bd2522e01a872056442e849c0e content_sha256=3685dfc0685f8af14d0267be5baa0fad7fe81e6c9673629e95b556c1e4b3d522 -->
# release

Release contract: isolated-session; reviewed-beta-backport; immutable-candidate; promote-without-rebuild; protected-ref-guard; non-destructive-release-identity.

Version bump and release. Args: major/first, minor/second, patch/third (default), or exact X.Y.Z.

Perform a version bump and release.

Parse argument:
- Empty or patch/third: bump patch (Z+1)
- minor/second: bump minor (Y+1, reset Z)
- major/first: bump major (X+1, reset Y and Z)
- X.Y.Z pattern: set exact version

Steps:
1. Read current version from simple.sdn (project.version)
2. Calculate new version
3. Update all locations:
   - simple.sdn (version: X.Y.Z)
   - VERSION file
   - src/app/cli/main.spl (hardcoded fallback in get_version())
   - src/app/cli/bootstrap_main.spl (hardcoded in bootstrap_version())
4. Update CHANGELOG.md with new section header
5. Commit
6. Tag: git tag -a vX.Y.Z
7. Ask before push — do NOT push without user approval

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
