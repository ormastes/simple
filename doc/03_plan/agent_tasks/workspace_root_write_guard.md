<!-- codex-research -->

# Workspace Root Write Guard - Detailed Implementation Plan

## Phase 1 - Policy and Audit

1. Add a workspace root guard module/script that reads `FILE.md`.
2. Parse allowed root entries from the root structure table.
3. Add explicit configuration for immediate child directory checks where
   `FILE.md` is not precise enough.
4. Implement `audit` and `--dry-run` output.
5. Add tests with synthetic workspaces and fixture `FILE.md` content.

Pitfalls:
- `FILE.md` is prose, so parsing must be conservative.
- Some root entries may be generated or platform-specific.
- Immediate child checks need configuration to avoid false positives.

## Phase 2 - Fix/Quarantine

1. Add `--fix` mode.
2. Move violations into `build/workspace_quarantine/<timestamp>/`.
3. Write a manifest mapping original path to quarantine path.
4. Never delete by default.

Pitfalls:
- Moving directories can be expensive.
- Quarantine must itself be an allowed path.
- Existing files in quarantine need collision-safe names.

## Phase 3 - Lint Integration

1. Wire audit mode into lint.
2. Emit stable diagnostics for root violations.
3. Fail lint on misplaced root entries.
4. Add lint tests for clean and dirty workspaces.

Pitfalls:
- Lint must not become a full-tree scanner.
- Diagnostics should point to `FILE.md` policy context.

## Phase 4 - Commit Hook

1. Add a repo hook script for added/renamed paths.
2. Check only staged/new paths where possible.
3. Block commits that introduce root-policy violations.
4. Document hook installation.

Pitfalls:
- Git and jj workflows differ.
- Hooks are local and can be bypassed, so lint/verify remains required.

## Phase 5 - Lock/Unlock

1. Add lock dry-run.
2. Save a restore manifest before changing permissions.
3. Implement Unix/macOS backend.
4. Implement Windows ACL backend with `icacls` or PowerShell.
5. Add unlock and manual recovery output.

Pitfalls:
- Over-broad locks can break builds and editors.
- Windows deny ACLs can override inherited allows.
- Elevated privilege must be explicit and recoverable.

## Phase 6 - Tool-Server Protection

1. Reuse existing file I/O protection concepts.
2. Deny or redirect writes into protected root paths.
3. Avoid shell-outs or full scans in hot request paths.
4. Measure startup, representative request latency, and RSS if MCP/LSP paths are
   changed.

Pitfalls:
- This only covers writes through guarded APIs.
- Cache invalidation must be explicit if policy is cached.

## Recommended Build Order

Implement phases 1-3 first, then phase 4. Add phase 5 after audit/fix is stable.
Add phase 6 last because it touches tool-server behavior and may require
performance verification.
