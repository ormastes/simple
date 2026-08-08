<!-- codex-research -->

# Workspace Root Write Guard - NFR Requirements

## Performance

NFR-001: Root and immediate-child audit should complete in under 1 second on a
normal developer workspace.

NFR-002: Lint integration should avoid full-tree scans unless explicitly
configured.

NFR-003: Tool-server write protection shall not add repeated full-tree scans,
repeated rereads, shell-outs, or retry sleeps to hot request paths.

## Safety

NFR-004: Fix mode shall quarantine by default, not delete.

NFR-005: Lock mode shall require dry-run output or an explicit force flag before
changing permissions.

NFR-006: Lock mode shall save a restore manifest sufficient for unlock.

NFR-007: Unlock shall be idempotent where the platform permits it.

NFR-008: If permissions cannot be restored automatically, the tool shall print
the exact manual recovery commands.

## Cross-Platform Behavior

NFR-009: Audit and fix shall work without elevated privileges on macOS, Linux,
and Windows when files are owned by the current user.

NFR-010: Unix/macOS lock/unlock shall use platform-appropriate permission or ACL
commands.

NFR-011: Windows lock/unlock shall use NTFS ACLs through `icacls` or PowerShell.

NFR-012: Platform-specific lock commands shall support dry-run previews.

## Integration

NFR-013: Lint shall report stable, actionable diagnostics with file paths and
policy source context.

NFR-014: Commit-hook checks shall run only against added or renamed paths when
possible.

NFR-015: CI/verify shall be able to run audit mode without mutating the
workspace.

NFR-016: MCP/tool-server protection, if implemented, shall include startup,
representative request latency, and RSS verification when hot paths are changed.

## Maintainability

NFR-017: Policy parsing shall be deterministic and tested with representative
`FILE.md` fixtures.

NFR-018: The implementation shall keep platform backends separated from policy
parsing and audit logic.

NFR-019: Error messages shall distinguish policy violations, permission failures,
and restore-manifest failures.
