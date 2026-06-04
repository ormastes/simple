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

## Common Simple Language Mistakes & Gotchas

The LSP server detects many of these automatically. Warnings appear as squiggly underlines with diagnostic codes.

### Critical Runtime Issues

| Mistake | What Happens | Fix |
|---------|-------------|-----|
| Mutating outer var in closure | Changes silently lost (capture-by-value) | Return modified value instead |
| `return` inside nested `match` | Return doesn't propagate, falls through | Extract inner match to helper function |
| `.push()` on module-level var from function | Array change not visible at module level | Use return values or local vars |
| Multiline `if` without parens | Parse failure or wrong behavior | Wrap: `if (a and`<br>`   b):` |

### Syntax Pitfalls

| Mistake | Diagnostic | Fix |
|---------|-----------|-----|
| `class Child(Parent)` | Error | No inheritance. Use composition, traits, or mixins |
| `StructName.new(args)` | DEPR002 | Use `StructName(field: value)` |
| `Type__method()` | DEPR001 | Use `Type.method()` |
| Bare `pass` | DEPR003 | Use `pass_do_nothing` or `pass_todo` |
| `s[:idx]` | Parse error | Use `s[0:idx]` |
| `s[:-1]` | Parse error | Use `s[0:s.len()-1]` |
| Chained methods `a.f().g()` | Runtime error | Use intermediate `var`: `var t = a.f(); t.g()` |

### Performance Anti-patterns (COLL warnings)

| Mistake | Code | Severity | Fix |
|---------|------|----------|-----|
| `arr = arr + [x]` in loop | COLL001 | Error | Use `.push(x)` |
| `str = str + x` in loop | COLL006 | Error | Collect to array, `.join()` |
| `.contains()` in loop | COLL002 | Warning | Use `Dict` for O(1) lookup |
| `.remove(0)` queue drain | COLL003 | Warning | Reverse + `.pop()` |
| Chained `.filter().filter()` | COLL005 | Warning | Combine predicates |

### LSP Diagnostic Codes

| Code | Meaning | Editor Rendering |
|------|---------|-----------------|
| UNUSED001-003 | Unused var/import/param | Faded (Unnecessary tag) |
| UNREACH001-003 | Unreachable code | Faded (Unnecessary tag) |
| DEPR001-003 | Deprecated syntax | Strikethrough (Deprecated tag) |
| COLL001-008 | Collection anti-patterns | Warning |
| CLOS001 | Closure modifies outer var | Warning |
| RET001 | Discarded return value | Info |
| BOOL001 | Multiline bool without parens | Warning |
| MEXH001-002 | Non-exhaustive match | Warning |
| ARG001-002 | Too many parameters (>7 warn, >12 error) | Warning/Error |
| DTYP001 | Duplicate typed args | Warning |
| STUB001-002 | Stub implementation | Faded (Unnecessary tag) |
| SAFE001/003 | Unsafe operation outside `unsafe` | Error |
| W0401-W0403 | Visibility violations | Warning |
| W0404 | Wide public API | Warning |
| W0406 | Star/wildcard import | Warning |

### Reserved Keywords

These cannot be used as variable/function names: `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`, `collect`, `shared`

### Quick Reference

- **Generics:** `Option<T>`, `List<Int>` (use `<>` not `[]`)
- **Optional check:** `value.?` (not `value?` or `is_some()`)
- **Null coalescing:** `value ?? default`
- **Error handling:** `Result<T, E>` + `?` operator (no try/catch)
- **Immutable preferred:** `val x = 1` or `x := 1` (walrus)
- **Mutable:** `var x = 1`
- **Method mutating self:** `me method_name()` (not `fn`)
- **String interpolation:** `"Hello {name}"` (default), `r"raw \d+"` (no interpolation)

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
