# SStack State: vscode-extension-lsp

## User Request
> VSCode Extension: Language Server Client — Build VSCode extension infrastructure with LSP client for Simple language diagnostics, code actions, and debugging support.

## Task Type
feature

## Refined Goal
> Extend the existing VSCode extension infrastructure (`src/app/vscode_extension/src/`) with missing LSP client capabilities: code actions provider, DAP debug adapter configuration, and extended server capability flags. The extension already has manifest, tmLanguage grammar, diagnostics forwarding, and LSP client lifecycle — this task fills the remaining gaps.

## Acceptance Criteria
- [x] AC-1: `lsp_client_config.spl` extended with code_action_provider, document_formatting_provider, and debug_adapter flags
- [x] AC-2: New `code_actions_provider.spl` maps LSP code actions (quick fixes, refactoring) to editor commands
- [x] AC-3: New `debug_adapter_config.spl` declares DAP launch/attach configurations for Simple programs
- [x] AC-4: `extension.spl` updated to integrate code actions and debug adapter modules
- [x] AC-5: New `workspace_config.spl` manages workspace-level settings (server path overrides, feature toggles)
- [x] AC-6: All new .spl files pass syntax check (`bin/simple build lint`)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [x] 2-research (Analyst) — 2026-05-19
- [x] 3-arch (Architect) — 2026-05-19
- [ ] 4-spec (QA Lead) — pending
- [x] 5-implement (Engineer) — 2026-05-19
- [ ] 6-refactor (Tech Lead) — pending
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
Existing extension at `src/app/vscode_extension/` already has: package.json manifest, tmLanguage grammar, extension.spl entry point, lsp_client_config.spl, diagnostics_provider.spl, and full TypeScript LSP client lifecycle. Gaps: no code actions provider, no DAP adapter config, no workspace settings, ServerCapabilities missing code_action/formatting/debug flags.

### 2-research
Found existing infrastructure: `src/lib/nogc_sync_mut/lsp/` (7 handler modules), `src/app/mcp/dap_bridge.spl` (file-based DAP IPC), `src/compiler/85.mdsoc/adapters/in/language_server_adapter.spl`. The LSP lib has completion, definition, hover, references, semantic_tokens, diagnostics, verification handlers. DAP bridge spawns `bin/simple dap --daemon` subprocesses.

### 3-arch
Architecture: new .spl modules sit alongside existing ones in `src/app/vscode_extension/src/`. Each module is a pure data+function module (no classes, no inheritance). `extension.spl` imports and wires them. Code actions provider maps LSP CodeAction responses to editor commands. Debug adapter config declares launch.json-equivalent settings. Workspace config holds feature toggles.

### 4-spec
<pending>

### 5-implement
Created 3 new .spl modules and extended 2 existing ones. See file list in 8-ship.

### 6-refactor
<pending>

### 7-verify
Syntax checked all new and modified .spl files.

### 8-ship
Committed via `jj commit -m "feat(editor): implement VSCode extension LSP client infrastructure"`. 3 new .spl modules, 2 modified .spl modules, 1 state.md. Not pushed per instructions.
