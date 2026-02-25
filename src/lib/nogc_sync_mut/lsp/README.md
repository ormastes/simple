# Simple Language Server (LSP)

Self-hosted Language Server Protocol implementation written in Simple language.

## Overview

This is the LSP server for Simple, written entirely in Simple itself. It provides:

- ✅ JSON-RPC 2.0 transport over stdin/stdout
- ✅ Document synchronization (didOpen, didChange, didClose)
- ✅ Real-time diagnostics (parse errors)
- ⏳ Code completion (TODO)
- ⏳ Go to definition (TODO)
- ⏳ Hover documentation (TODO)
- ⏳ Find references (TODO)

## Architecture

```
main.spl          # Entry point, CLI argument handling
server.spl        # Server state and request handlers
protocol.spl      # LSP message types and structures
transport.spl     # JSON-RPC over stdio (Content-Length protocol)
```

## Building

```bash
# Build from project root
./simple/build_tools.sh

# Binary will be at:
./simple/bin_simple/simple_lsp
```

## Usage

The LSP server communicates via stdin/stdout using JSON-RPC 2.0:

```bash
# Run the server (typically started by editor)
./simple/bin_simple/simple_lsp

# Enable debug logging
SIMPLE_LSP_DEBUG=1 ./simple/bin_simple/simple_lsp
```

## Editor Integration

### VS Code

Add to `.vscode/settings.json`:

```json
{
  "simple.lsp.path": "path/to/simple/bin_simple/simple_lsp",
  "simple.lsp.enable": true
}
```

### Neovim

Using `nvim-lspconfig`:

```lua
local lspconfig = require('lspconfig')

lspconfig.simple.setup{
  cmd = { 'path/to/simple/bin_simple/simple_lsp' },
  filetypes = { 'simple', 'spl' },
  root_dir = lspconfig.util.root_pattern('simple.toml', '.git'),
}
```

## Protocol Support

### Lifecycle

- ✅ `initialize` - Initialize server
- ✅ `initialized` - Confirm initialization
- ✅ `shutdown` - Shutdown request
- ✅ `exit` - Exit notification

### Text Document Synchronization

- ✅ `textDocument/didOpen` - Document opened
- ✅ `textDocument/didChange` - Document changed (full sync)
- ✅ `textDocument/didClose` - Document closed

### Diagnostics

- ✅ `textDocument/publishDiagnostics` - Send diagnostics to client

### Code Intelligence (TODO)

- ⏳ `textDocument/completion` - Code completion
- ⏳ `textDocument/definition` - Go to definition
- ⏳ `textDocument/hover` - Hover information
- ⏳ `textDocument/references` - Find references
- ⏳ `textDocument/documentSymbol` - Document symbols
- ⏳ `textDocument/semanticTokens` - Semantic highlighting

## Implementation Details

### Transport Layer (`transport.spl`)

Implements Content-Length protocol:

```
Content-Length: 123\r\n
\r\n
{"jsonrpc":"2.0",...}
```

Functions:
- `read_message()` - Read JSON-RPC message from stdin
- `write_message(data)` - Write message to stdout
- `write_response(id, result)` - Write response
- `write_notification(method, params)` - Write notification

### Protocol Types (`protocol.spl`)

LSP data structures:
- `Position` - Line/character position
- `Range` - Text range
- `Diagnostic` - Error/warning message
- `TextDocumentIdentifier` - Document reference
- `JsonRpcRequest/Response/Notification` - JSON-RPC messages

### Server Logic (`server.spl`)

Server state management:
- `ServerState` - Uninitialized/Initialized/ShuttingDown
- `DocumentInfo` - Cached document content
- `LspServer` - Main server class with handlers

Request handlers:
- `handle_initialize()` - Server initialization
- `handle_shutdown()` - Graceful shutdown
- `handle_did_open/change/close()` - Document sync
- `publish_diagnostics()` - Send diagnostics

## Current Limitations

1. **Full sync only** - Re-parses entire document on change (no incremental)
2. **Basic diagnostics** - Simple pattern matching (no full parser integration yet)
3. **No cross-file analysis** - Each file analyzed independently
4. **No workspace support** - Single-file mode only

## Roadmap

### Phase 1: Core Protocol ✅
- ✅ JSON-RPC transport
- ✅ Server lifecycle
- ✅ Document synchronization
- ✅ Basic diagnostics

### Phase 2: Parser Integration (In Progress)
- ⏳ Full AST-based parsing
- ⏳ Type checking integration
- ⏳ Semantic diagnostics
- ⏳ Symbol table construction

### Phase 3: Code Intelligence
- ⏳ Completion (keywords, identifiers, members)
- ⏳ Go to definition
- ⏳ Hover documentation
- ⏳ Find references
- ⏳ Rename symbol

### Phase 4: Advanced Features
- ⏳ Incremental parsing
- ⏳ Workspace support
- ⏳ Semantic tokens (highlighting)
- ⏳ Code actions (quick fixes)
- ⏳ Formatting integration

## Testing

Manual testing with LSP client:

```bash
# Send initialize request
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | \
  ./simple/bin_simple/simple_lsp

# Expected response with server capabilities
```

Integration testing via editor:
1. Configure editor to use `simple_lsp`
2. Open a `.spl` file
3. Make changes and observe diagnostics

## Debugging

Enable debug logging:

```bash
export SIMPLE_LSP_DEBUG=1
./simple/bin_simple/simple_lsp
```

Debug messages will appear on stderr (won't interfere with JSON-RPC on stdout).

## References

- [LSP Specification](https://microsoft.github.io/language-server-protocol/)
- [JSON-RPC 2.0](https://www.jsonrpc.org/specification)
- Status: `doc/status/lsp_implementation.md`
- Features: `doc/features/postponed_feature.md` (#1359-#1365)

## Contributing

To add new LSP features:

1. Add protocol types to `protocol.spl`
2. Implement handler in `server.spl`
3. Update dispatcher in `handle_request()` or `handle_notification()`
4. Test with real editor
5. Update this README and status docs
