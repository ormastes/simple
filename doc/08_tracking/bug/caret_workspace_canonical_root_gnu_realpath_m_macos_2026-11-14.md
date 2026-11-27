# Caret workspace canonicalised its worktree root with GNU-only `realpath -m` (2026-11-14)

**Symptom (macOS 26.5 arm64; any BSD userland):**
`test/03_system/app/llm_caret/agent_team_workspace_system_spec.spl` failed 0/1
with `expected <...>/agent_team_lifecycle/repo to equal ` (empty right side), and
`caret_agent_infra_acceptance_spec.spl` carried the same comparison.

**Root cause:** BSD `realpath` has no `-m` (`realpath: illegal option -- m`,
exit 1, empty stdout). Two sites depended on it:
- product: `_canonical` in `src/app/llm_caret/agent_workspace.spl:85` ran
  `realpath -m <root>` and silently kept the raw text on failure, so on macOS a
  worktree root reached through a symlink (`/tmp` -> `/private/tmp`) was never
  canonicalised and `worktree_path` disagreed with `git worktree list`;
- specs: both system specs computed their expected path with `realpath -m repo`
  (`agent_team_workspace_system_spec.spl:154`,
  `caret_agent_infra_acceptance_spec.spl:166`) and compared against `""`.

**Fix:** `_canonical` resolves the deepest EXISTING ancestor with plain
`realpath` (POSIX-portable) and appends the missing tail; a relative root with
no existing component is anchored at the cwd, matching `-m`. The two specs use
plain `realpath` on the repo, which exists at that point; the assertion is
unchanged.

**Specs** (`test/01_unit/app/llm_caret/agent_workspace_spec.spl`)
- Reproducer: "names a tree the way git does when the not-yet-created root sits
  behind a symlink".
- Generalization: "resolves the deepest existing ancestor and keeps the missing
  tail of a worktree root" (multi-level missing tail, existing root, relative root).
- A/B on macOS, same tree and binary, only `agent_workspace.spl` toggled:
  6 passed / 2 failed before, 8 passed / 0 failed after.
- System: `agent_team_workspace_system_spec.spl` 0/1 -> 1/1.

**BSD:** plain `realpath <existing path>` exists on FreeBSD; not run on the VM.
**Windows:** GNU `realpath` (Git for Windows) accepts the plain form; not re-run.
