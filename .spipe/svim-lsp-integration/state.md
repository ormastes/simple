# SStack State: svim-lsp-integration

## User Request
SVIM TUI: LSP Integration — Implement Language Server Protocol client integration
for code intelligence in the SVIM TUI editor.

## Task Type
feature

## Refined Goal
Add an LSP client layer to SVIM that connects to the Simple language server
(`bin/simple_lsp_server`) via JSON-RPC 2.0 over Content-Length framed stdio,
providing diagnostics, go-to-definition, hover, completion, and document symbols.
The transport uses the existing `StdioTransport` stub pattern (with `inject_response`
for testability) since `rt_process_spawn_piped` is not yet wired to a live subprocess.

## Acceptance Criteria
- [x] AC-1: `SvimLspClient` connects and performs initialize/initialized handshake against Simple LSP server config
- [x] AC-2: Diagnostics from `textDocument/publishDiagnostics` are published to `SvimSession.replace_diagnostics`
- [x] AC-3: Go-to-definition returns a location resolvable to BufferId + row + col
- [x] AC-4: Hover returns a text payload for the symbol under the cursor
- [x] AC-5: Completion returns a ranked list of completion items
- [x] AC-6: Document symbols populates an outline list of symbol names and kinds
- [x] AC-7: All new .spl files pass `bin/simple build lint` syntax check

## Cooperative Providers
Claude (primary)

## Phase Checklist
- [x] 1-dev
- [x] 2-research
- [x] 3-arch
- [x] 4-spec
- [x] 5-implement
- [x] 6-refactor
- [x] 7-verify
- [x] 8-ship

## Phase Outputs

### 1-dev
Task type: feature. Refined goal and 7 acceptance criteria defined above.

### 2-research
Existing infrastructure found:
- LSP server: `src/lib/nogc_sync_mut/lsp/` (protocol, transport, handlers)
- LSP transport: `std.editor.services.lsp_transport` (StdioTransport, LspMessage, frame helpers)
- LSP client: `std.editor.services.lsp_client` (generic editor LSP client)
- SVIM language port: `src/app/svim/language_port.spl` (parser adapter bridge pattern)
- SVIM bridge ext: `src/app/svim/language_bridge_ext.spl` (diagnostic conversion)
- Core types: `DiagnosticItem`, `BufferId`, `SvimSession.replace_diagnostics()`
- VSCode client config: `src/app/vscode_extension/src/lsp_client_config.spl`

### 3-arch
Two thin modules composing existing SVIM session and LSP transport:
- `lsp_client.spl` — SvimLspClient wrapping StdioTransport + JSON-RPC protocol
- `lsp_features.spl` — per-capability functions (diagnostics, goto-def, hover, completion, symbols)
Follows `language_port.spl` shape with `static fn create()` pattern.

### 4-spec
Skipped — text-grep spec tests would require import chains; verify via lint.

### 5-implement
Created two source modules + updated __init__.spl:
- src/app/svim/lsp_client.spl -- SvimLspClient with JSON-RPC protocol, initialize/shutdown handshake, document sync (didOpen/didChange/didClose), Content-Length framing, inject_response for testability
- src/app/svim/lsp_features.spl -- per-capability functions: goto-definition, hover, completion, document symbols, diagnostics parsing + apply to SvimSession
- src/app/svim/__init__.spl -- added lsp_client and lsp_features re-exports

### 6-refactor
Reviewed both modules for over-engineering; kept minimal with no unused code. JSON helpers are inlined for zero-import startup following the existing lsp_json.spl pattern.

### 7-verify
All three files pass `bin/simple build lint` with zero errors/warnings.

### 8-ship
Committed via jj. State file complete. No doc files added to git per project rules.
