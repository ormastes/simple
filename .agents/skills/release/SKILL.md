---
name: release
description: Version bump and release. Accepts version argument (major/first, minor/second, patch/third, or exact X.Y.Z). Defaults to patch. Updates all version locations, CHANGELOG, commits, tags, asks before push.
---

# Release — Version Bump and Tag

## Usage

- No args or `patch`/`third`: bump patch (0.9.3 -> 0.9.4)
- `minor`/`second`: bump minor (0.9.3 -> 0.10.0)
- `major`/`first`: bump major (0.9.3 -> 1.0.0)
- `X.Y.Z`: set exact version

## Steps

1. Read current version from `simple.sdn` (field `project.version`)
2. Calculate new version
3. Update all version locations:
   - `simple.sdn` — `version: X.Y.Z`
   - `VERSION` — entire file
   - `src/app/cli/main.spl` — hardcoded fallback in `get_version()`
   - `src/app/cli/bootstrap_main.spl` — hardcoded in `bootstrap_version()`
4. Update `CHANGELOG.md` with new section
5. Commit: `jj commit -m "chore: release vX.Y.Z"` (or `git commit`)
6. Tag: `git tag -a vX.Y.Z -m "Release vX.Y.Z"`
7. Ask before push — do NOT push without user approval

## Prerequisite

Run $verify first — must show STATUS: PASS.
SPipe must already be complete and verified. Do not create or update SPipe in
release; if SPipe is missing/stale, return to verify/implementation.

## Push

After commit/tag, ask before pushing. If approved, use jj linear sync:

```bash
FILE_COUNT_BEFORE=$(git ls-files | wc -l | tr -d ' ')
jj git fetch
jj rebase -d main@origin
FILE_COUNT_AFTER=$(git ls-files | wc -l | tr -d ' ')
test "$FILE_COUNT_AFTER" -ge "$FILE_COUNT_BEFORE"
jj bookmark set main -r @-
jj git push --bookmark main
git push --tags
```
