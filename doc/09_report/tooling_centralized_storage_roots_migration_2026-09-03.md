# Tooling Centralized Storage Roots Migration

**Date:** 2026-09-03  
**Status:** implemented in isolated fork

## Migrated producers

- Tooling daemon session, diagnostics, socket, temporary, and identity-safe index paths.
- SVIM/editor worktree-local session paths.
- MCP CLI output, Caret payload, editor state, and DAP child-process storage.
- VS Code CLI and LSP child environments plus DAP session configuration.

## Policy

- Reusable indexes and caches require an explicit schema and identity and derive only from `SIMPLE_USER_STORAGE_ROOT`.
- Sessions, diagnostics, sockets, outputs, and temporary payloads derive only from `SIMPLE_WORKTREE_STORAGE_ROOT`.
- Spawned Simple children receive a deterministic allowlisted storage environment.
- Missing root authority produces a typed/degraded failure; no `/tmp`, `TMP`, or `TEMP` fallback is used.
- Ambient root discovery is cached after the first successful resolution.

## Evidence

- `centralized_storage_roots_spec.spl`: 3 passed, 0 failed.
- `caret_tools_mcp_system_spec.spl`: 3 passed, 0 failed.
- VS Code TypeScript compile and webview build: passed.
- Direct environment working-tree guard: passed.
- Owned-path scan found no production `/tmp`, legacy Caret temp, DAP temp, or direct child `process.env` launch path.

VS Code Extension Host execution was attempted after a locked `npm ci`, but the downloaded test application lacked its expected Electron executable and failed with `ENOENT`. No test PASS is claimed for that external host lane.

The deployed pure-Simple runtime still returns the previously recorded launcher `-1` failure for broad `check` commands, so broad source checks are not claimed. Focused interpreter execution compiled the migrated modules and passed.
