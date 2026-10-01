# Centralized Storage Orchestration Migration

- Scope: `bin/codex`, Codex guard, `scripts/spipe`, and explicit worktree/session helpers only.
- Managed agent worktrees: `${SIMPLE_USER_STORAGE_ROOT}/worktrees/agents`.
- Cross-worktree Codex session locks: `${SIMPLE_USER_STORAGE_ROOT}/state/codex-session-locks`.
- Per-run Codex, SPipe, stdlib-probe, and test-session scratch: `${SIMPLE_WORKTREE_STORAGE_ROOT}/tmp/<operation>/run.<identity>`.
- Ownership: both roots use `.simple-storage-root-v1`; managed worktrees use `.simple-managed-worktree-v1`; active run directories carry live leases.
- Cleanup: only validated worktree `tmp/<operation>/run.*` descendants are removable; live leases, unsafe roots, unmarked managed worktrees, and managed worktrees with live leases are refused.

## Focused Evidence

- Shell syntax: passed before the final process-match correction.
- Storage-root placement/marker/lease/cleanup mutation test: passed.
- Stdlib invoking-worktree self-test: passed in the earlier focused sequence before a later test aborted.
- Test-session budget self-test: passed in the earlier focused sequence before a later test aborted.
- Codex guard regression: the existing direct-resume fixture failed because its process matching remained command-layout dependent. A final full-line portable matcher was applied after reaching the mandatory three-cycle cap and is intentionally not claimed as rerun.

The lane therefore commits implementation and evidence without claiming full verification. A fresh integration session must rerun `scripts/check/codex-run-guard-test.shs` once.
