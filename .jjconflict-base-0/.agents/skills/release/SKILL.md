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

1. Read current version from the root `VERSION` file
2. Calculate new version
3. Update all version locations:
   - `VERSION` — entire file
   - `src/app/cli/cli_helpers.spl` — hardcoded fallback in `get_version()`
   - `src/app/cli/_CliMain/args_and_os_commands.spl` — hardcoded fallback in `get_version()`
   - `src/app/cli/bootstrap_main.spl` — hardcoded in `bootstrap_version()`
4. Update `CHANGELOG.md` with new section
5. Commit: `jj commit -m "chore: release vX.Y.Z"`
6. Tag: `git tag -a vX.Y.Z -m "Release vX.Y.Z"`
7. Ask before push — do NOT push without user approval

## Prerequisite

Run $verify first — must show STATUS: PASS.
After bootstrap, run `bin/simple test test --whole --mode=interpreter`; it is a
release blocker for all specs/long tests, `.spl` comment doctests, and
configured Markdown code fences.
For SimpleOS mission-critical releases, also run
`sh scripts/check/check-simpleos-mission-critical-release.shs`; do not release
while it reports blocked or failed, and PASS requires `release_blockers=none`.
SPipe must already be complete and verified. Do not create or update SPipe in
release; if SPipe is missing/stale, return to verify/implementation.
Generated-manual quality and lower-model sidecar review must already be covered
by verify PASS; release does not repair or accept them afterward.
Workflow/tooling/evidence/spec/verification contract docs must already be fresh
from verify; release must not repair stale `doc/07_guide`, `doc/06_spec`,
`.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`,
or `.gemini/commands` instructions.
`find doc/06_spec -name '*_spec.spl' | wc -l` must return `0`.

## Push

After commit/tag, ask before pushing. If approved, use jj linear sync:

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
