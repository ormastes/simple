<!-- codex-design -->

# Workspace Root Write Guard Architecture

## Layers

1. Policy extraction: `scripts/check-workspace-root-guard.shs` reads root
   `FILE.md` and derives allowed root entries plus declared immediate-child
   paths.
2. Audit/fix: the same script audits root and max-depth-2 paths, skips ignored
   VCS state, and quarantines violations in `build/workspace_quarantine/` when
   `fix` is requested.
3. Integration gates: `bin/simple build lint` runs staged audit before the
   normal runtime lint path. `scripts/hooks/pre-commit` runs the same staged
   audit for Git hooks.
4. Permission backend: `lock` and `unlock` currently emit platform-specific
   restore and lock commands. They do not mutate permissions by default.
5. Tool-server guard: MCP file I/O already has in-memory protection rules. The
   root guard remains outside hot request paths; future MCP work should preload
   exact/prefix rules once and guard atomic writes.

## Design Constraints

- Full audit may expose existing untracked local drift; staged audit is used for
  lint and hooks to prevent new violations without breaking current worktrees.
- Fix mode moves to quarantine and never deletes.
- Windows lock behavior is ACL-based through Administrator `icacls`, not sudo.
- Unix/macOS lock behavior is permission/ACL based and must preserve a restore
  manifest before mutation.

## Performance

The audit precomputes allowed, tracked, and ignored path sets into temp files and
uses a single `awk` pass over root/max-depth-2 paths. No full-tree scan is used
for lint or hook mode.
