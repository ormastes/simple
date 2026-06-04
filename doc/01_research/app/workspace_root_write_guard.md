<!-- codex-research -->

# Workspace Root Write Guard - Local Research

## Goal

Prevent accidental dirty files and directories in the repository root and in
immediate root child directories, using `FILE.md` as the canonical policy.
Provide a script that can read the root `FILE.md`, detect misplaced files or
directories, and optionally fix or lock down the workspace.

## Existing Repo Policy

`FILE.md` is the canonical structure definition. It lists allowed root entries
and explicitly says:

- Only the listed root files belong at repository root.
- No other files at root.
- Temporary files, build artifacts, compiler intermediates, and generated files
  must go in the documented subdirectories.
- `doc/` subdirectories must be numbered.
- Code files are `.spl` or `.shs`.

The policy is human-readable today. There is no discovered script that parses
`FILE.md` into an enforceable allowlist for root and immediate child entries.

## Existing Guard Infrastructure

`src/compiler/35.semantics/lint/critical_file_guard.spl` reads
`config/critical_files.sdn` and emits warnings/errors for deleted or shrunk
critical files. It covers preservation of important files, not creation of new
misplaced files.

`doc/07_guide/lint_export_and_critical_file_guard.md` documents that guard and
its `protected_dirs` configuration.

`src/lib/nogc_async_mut/mcp/fileio_protection.spl` provides rule-based file
operation protection with allow, protect, and redirect behavior. That is useful
prior art for tool-server writes, but it does not protect arbitrary shell,
editor, build, or agent writes.

`src/lib/*/file_system/permissions.spl` has Unix-style permission helpers such
as making files read-only or writable. The current helpers are library-level and
mock/simplified in places; they are not enough by themselves for host workspace
ACL enforcement.

## Implementation Surfaces

A complete solution should be layered:

1. Policy extraction: parse root `FILE.md` into allowed root entries and
   optionally allowed immediate child entries.
2. Audit: scan repository root and one level below root children for entries
   not allowed by policy.
3. Fix: move unknown entries to a quarantine directory such as
   `build/workspace_quarantine/` or delete only with explicit confirmation.
4. Permission lock: make root and selected immediate child directories
   non-writable for normal user processes while preserving write access to
   approved mutable directories.
5. Verification: add tests with synthetic workspaces and avoid depending on
   host-specific permissions for normal unit tests.

## Risks

Repository roots must remain writable enough for VCS metadata, generated
artifacts under allowed directories, package managers, and build tools. A blunt
recursive read-only mode would break normal development. The safer default is
audit/fix first, then an opt-in lock mode for environments where the user is
ready to grant elevated privileges.

Windows requires ACL handling rather than Unix `chmod`. The script should use
platform-specific backends instead of pretending one permission model works
everywhere.

## Recommendation

Build a host-side workspace hygiene tool, likely under `scripts/`, that reads
`FILE.md`, audits root plus immediate root child directories, fixes violations
by moving them to quarantine, and offers opt-in permission lock/unlock commands.
Integrate the audit into lint/verify before enabling lock mode by default.
