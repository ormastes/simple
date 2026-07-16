---
name: release
description: "Codex release skill. Version bump (major/minor/patch/exact), CHANGELOG update, commit, tag, push (ask before push). Prerequisite: verify PASS."
---

# Release — Codex Version Bump and Tag

**Cooperative Phase:** Release (after verification passes)
**Self-sufficient.** Can be run by any LLM independently.

## Tools

- **Simple MCP** — read/write project files

## Usage

- No args or `patch`/`third`: bump patch (0.9.3 -> 0.9.4)
- `minor`/`second`: bump minor (0.9.3 -> 0.10.0)
- `major`/`first`: bump major (0.9.3 -> 1.0.0)
- `X.Y.Z`: set exact version

## Prerequisite

Run `verify` skill first — must show **STATUS: PASS**.

Run `bin/simple test test --whole --mode=interpreter` after bootstrap and
before changing versions or tags. This release-blocking command includes the
full spec/long-test surface, `.spl` comment doctests, and executable Markdown
code fences; any failure stops release.

Do NOT proceed with release if verification has any FAIL items.
For SimpleOS mission-critical releases, also run
`sh scripts/check/check-simpleos-mission-critical-release.shs`; do not release
while it reports blocked or failed, and PASS requires `release_blockers=none`.

SPipe specs and SPipe coverage are verified before release. Do not create,
rewrite, or weaken SPipe during release; if SPipe is missing, stale, or
placeholder-based, stop and go back to verify/implementation.
Generated-manual quality and lower-model sidecar review must already be covered
by verify PASS; release does not repair or accept them afterward.
Workflow/tooling/evidence/spec/verification contract docs must already be fresh
from verify; release must not repair stale `doc/07_guide`, `doc/06_spec`,
`.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`,
or `.gemini/commands` instructions.

## Steps

### 1. Read Current Version
Read from the root `VERSION` file.

### 2. Calculate New Version
Apply bump rule (major/minor/patch) or use exact version.

### 3. Update All Version Locations

| File | Field/Pattern |
|------|---------------|
| `VERSION` | Entire file content |
| `src/app/cli/main_part1.spl` | Hardcoded fallback in `get_version()` |
| `src/app/cli/bootstrap_main.spl` | Hardcoded in `bootstrap_version()` |

### 4. Update CHANGELOG

Add new section to `CHANGELOG.md`:

```markdown
## [X.Y.Z] - YYYY-MM-DD

### Added
- <new features>

### Changed
- <modifications>

### Fixed
- <bug fixes>
```

Populate from recent commits since last release tag.

### 5. Commit

```bash
jj commit -m "chore: release vX.Y.Z"
```

### 6. Tag

```bash
git tag -a vX.Y.Z -m "Release vX.Y.Z"
```

### 7. Sync and Push (ASK FIRST)

**Do NOT push without user approval.**

Ask: **"Ready to push vX.Y.Z to remote? (y/n)"**

If approved:
```bash
FILE_COUNT_BEFORE=$(git ls-files | wc -l | tr -d ' ')
jj git fetch
jj rebase -d main@origin
FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')
test "$FILE_COUNT_AFTER" -ge "$FILE_COUNT_BEFORE"
jj bookmark set main -r @-
env -u GITHUB_TOKEN -u GH_TOKEN jj git push --bookmark main
env -u GITHUB_TOKEN -u GH_TOKEN git push --tags
```

If HTTPS auth fails, do not print tokens or embed them in remote URLs. Run
`env -u GITHUB_TOKEN -u GH_TOKEN gh auth setup-git` when the stored GitHub CLI
credential should be used; stale `GH_TOKEN` or `GITHUB_TOKEN` values can
override that credential.

## Artifacts Produced

| Artifact | Path |
|----------|------|
| Updated version | `VERSION`, `src/app/cli/main_part1.spl`, `src/app/cli/bootstrap_main.spl` |
| Changelog | `CHANGELOG.md` |
| Git tag | `vX.Y.Z` |

## Rules

- NEVER release without verify PASS
- NEVER release SimpleOS mission-critical artifacts while
  `check-simpleos-mission-critical-release.shs` is blocked or failed, or lacks
  `release_blockers=none`
- NEVER update SPipe in release; release must consume verified SPipe evidence
- NEVER accept generated-manual quality or sidecar-review gaps during release
- NEVER push without user approval
- NEVER skip version locations — all 3 version sources must be updated
- NEVER release if `find doc/06_spec -name '*_spec.spl' | wc -l` is nonzero
- All code in `.spl` — no Python, no Bash
