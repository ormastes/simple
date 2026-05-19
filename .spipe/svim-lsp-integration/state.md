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
- [ ] AC-1: `SvimLspClient` connects and performs initialize/initialized handshake against Simple LSP server config
- [ ] AC-2: Diagnostics from `textDocument/publishDiagnostics` are published to `SvimSession.replace_diagnostics`
- [ ] AC-3: Go-to-definition returns a location resolvable to BufferId + row + col
- [ ] AC-4: Hover returns a text payload for the symbol under the cursor
- [ ] AC-5: Completion returns a ranked list of completion items
- [ ] AC-6: Document symbols populates an outline list of symbol names and kinds
- [ ] AC-7: All new .spl files pass `bin/simple build lint` syntax check

## Cooperative Providers
Claude (primary)

## Phase Checklist
- [x] 1-dev
- [x] 2-research
- [x] 3-arch
- [ ] 4-spec
- [ ] 5-implement
- [ ] 6-refactor
- [ ] 7-verify
- [ ] 8-ship

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
(pending)

### 6-refactor
(pending)

### 7-verify
(pending)

### 8-ship
(pending)
