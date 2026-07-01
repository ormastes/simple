<!-- codex-design -->

# Workspace Root Write Guard Architecture

## Layers

1. Policy extraction: `scripts/check-workspace-root-guard.shs` reads root
   `FILE.md` and derives allowed root entries plus declared immediate-child
   paths. It then walks the linked manifest tree — each child FILE.md that is
   referenced in its parent's `## Child Manifests` section adds enforcement for
   that directory.
2. Audit/fix: the same script audits paths at all governed depths, skips ignored
   VCS state, and quarantines violations in `build/workspace_quarantine/` when
   `fix` is requested.
3. Integration gates: `bin/simple build lint` runs staged audit before the
   normal runtime lint path. `.git/hooks/pre-commit` runs the staged audit
   (installed via `scripts/setup/install-workspace-guard-hook.shs --apply`).
4. Permission backend: `lock` and `unlock` currently emit platform-specific
   restore and lock commands. They do not mutate permissions by default.
5. Tool-server guard: MCP file I/O already has in-memory protection rules. The
   root guard remains outside hot request paths; future MCP work should preload
   exact/prefix rules once and guard atomic writes.

## Recursive Manifest Tree

FILE.md files form a tree rooted at the project root. Each FILE.md can link to
child manifests via a `## Child Manifests` section. Only linked manifests enforce
their directory — an orphan FILE.md (not referenced by its parent) is documentary
only.

Error codes:
- **WRG001**: Root entry not allowed by `FILE.md`
- **WRG002**: Immediate root child not declared by `FILE.md` `## dir/` section
- **WRG003**: Deeper entry not declared by a linked child `FILE.md`

## Design Constraints

- Full audit may expose existing untracked local drift; staged audit is used for
  lint and hooks to prevent new violations without breaking current worktrees.
- Fix mode moves to quarantine and never deletes.
- Windows lock behavior is ACL-based through Administrator `icacls`, not sudo.
- Unix/macOS lock behavior is permission/ACL based and must preserve a restore
  manifest before mutation.
- Recursive enforcement only applies to linked manifests — stray FILE.md files
  do not accidentally break the build.

## Performance

The audit precomputes allowed, tracked, ignored, and manifest-tree path sets into
temp files and uses a single `awk` pass over all governed paths. Depth is bounded
by the manifest tree depth (typically 2-3 levels). No full-tree scan is used for
lint or hook mode.
