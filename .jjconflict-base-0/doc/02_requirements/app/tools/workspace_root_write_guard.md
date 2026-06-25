<!-- codex-research -->

# Workspace Root Write Guard - Feature Requirements

## Scope

Implement a policy-driven guard that prevents or detects accidental files and
directories in the repository root and in configured immediate root child
directories. The root `FILE.md` is the canonical policy source.

## Requirements

REQ-001: The tool shall parse root `FILE.md` to derive allowed root entries.

REQ-002: The tool shall audit repository root entries and report files or
directories not allowed by `FILE.md`.

REQ-003: The tool shall audit configured immediate root child directories for
unexpected files or directories.

REQ-004: The tool shall provide a dry-run mode that reports violations without
changing files.

REQ-005: The tool shall provide a fix mode that moves violations to an allowed
quarantine directory instead of deleting by default.

REQ-006: Lint shall run the root write guard audit and fail on misplaced root
entries.

REQ-007: A commit hook shall block newly added files or directories that violate
the root write guard policy.

REQ-008: The tool shall provide opt-in lock and unlock commands for protected
directories.

REQ-009: Unix/macOS lock mode shall use host permissions or ACLs and shall save
a restore manifest before changing permissions.

REQ-010: Windows lock mode shall use Windows ACLs through `icacls` or PowerShell
and shall save a restore manifest before changing ACLs.

REQ-011: Lock/unlock operations that require elevated privilege shall request or
document the required privilege explicitly. Windows shall use Administrator
privilege rather than `sudo`.

REQ-012: Tool-server file writes shall be denied or redirected when they target
protected root paths, where this can be done without unacceptable startup or hot
request overhead.

REQ-013: The implementation shall keep known mutable directories writable, such
as build/cache/temp directories allowed by `FILE.md`.

REQ-014: The guard shall never delete user files unless a future explicit
destructive mode is designed and confirmed.

REQ-015: The guard shall include tests for policy parsing, audit, fix/quarantine,
lint integration, hook behavior, and platform command generation.

## Out of Scope

Recursive protection of every repository directory is out of scope for the
first implementation unless explicitly configured.

Changing VCS internals or blocking writes inside `.git`/`.jj` is out of scope.
