<!-- llm-process-gen: managed source=claude_release_command source_sha256=8101a3f942cf7248127ec5931807a5fd55425fb7bfb11ea1aedfaa70a7a6551b content_sha256=861814efcb71cb4d3344e56009aaefefe93af4452886d06d8ca671c9faff85da -->
# Release Skill

Release contract: isolated-session; reviewed-beta-backport; immutable-candidate; promote-without-rebuild; protected-ref-guard; non-destructive-release-identity.

## Usage

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

## Procedure

Given argument: `$ARGUMENTS`

Prerequisite: `/verify` must show `STATUS: PASS`. SPipe/manual evidence,
lower-model sidecar review, and workflow/tooling/evidence/spec/verification
contract docs must already be complete from verify. Release must not create or
update SPipe specs, repair generated-manual quality, accept sidecar-review gaps,
or repair stale `doc/07_guide`, `doc/06_spec`, `.codex/skills`,
`.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, or
`.gemini/commands` instructions. Before proceeding, confirm
`find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`.

## Scoped self-review status and remediation

1. Read current version from `simple.sdn` (field `project.version`, line 6)
2. Parse argument:
   - Empty, `patch`, or `third` → increment patch (Z+1)
   - `minor` or `second` → increment minor (Y+1), reset patch to 0
   - `major` or `first` → increment major (X+1), reset minor and patch to 0
   - Pattern `X.Y.Z` (digits.digits.digits) → use as-is
   - Anything else → error, show usage
3. Print: `Version bump: {old} → {new}`

### Step 2 — Update all version locations

Update these 4 files with the new version:

| File | What to change |
|------|---------------|
| `simple.sdn` | `version: X.Y.Z` (line 6) |
| `VERSION` | Entire file content: `X.Y.Z\n` |
| `src/app/cli/main.spl` | Hardcoded fallback string `"X.Y.Z"` in `get_version()` |
| `src/app/cli/bootstrap_main.spl` | Hardcoded string `"X.Y.Z"` in `bootstrap_version()` |

### Step 3 — Update CHANGELOG

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
