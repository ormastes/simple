# Compiler Query API Guide

**Location**: `src/compiler/query_api.spl`
**Purpose**: Provide IDE tooling integration (LSP) with compiler state queries
**Status**: Phase 1 - API Design Complete ✅

---

## Overview

The Compiler Query API provides a high-level interface for IDE tools to query compiler state without directly manipulating internal compiler data structures. It's designed to support Language Server Protocol (LSP) features like:

- Code completion
- Go to definition
- Find references
- Hover information
- Document symbols
- Diagnostics

## Architecture

```
┌─────────────────────────────────────┐
│      LSP Server (lsp/server.spl)    │
│   (textDocument/completion, etc.)   │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│   Compiler Query API (query_api.spl │
│   - CompilerQueryContext            │
│   - Caching & invalidation          │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│     Compiler Internal APIs          │
│  - Parser (rust/parser/)            │
│  - Symbol tables (dependency/)      │
│  - Type inference (inference/)      │
└─────────────────────────────────────┘
```

## Core Concepts

### 1. CompilerQueryContext

The main entry point for all queries. Maintains cached state for fast responses.

```simple
import compiler.query_api

# Create context for a project
val ctx = CompilerQueryContext.create("/path/to/project")

# Query symbol at position
val symbol = ctx.symbol_at("src/main.spl", Position(line: 10, column: 5))

# Get completions
val completions = ctx.completions_at("src/main.spl", Position(line: 15, column: 10))

# Get diagnostics
val diagnostics = ctx.get_diagnostics("src/main.spl")
```

### 2. Caching Strategy

The query context caches:
- **Parsed ASTs** - Avoid re-parsing unchanged files
- **Symbol tables** - Avoid re-resolving symbols
- **Type inference results** - Avoid re-running type checker
- **Diagnostics** - Reuse diagnostic computations

Cache invalidation happens when:
- File modification time changes
- Explicit invalidation via `ctx.invalidate_file(path)`

### 3. Position-Based Queries

All queries use 0-based line/column positions:

```simple
struct Position:
    line: i64    # 0-based line number
    column: i64  # 0-based column (UTF-8 byte offset)
```

## API Reference

### Context Creation

```simple
# Create context for a project root
static fn CompilerQueryContext.create(project_root: text) -> CompilerQueryContext

# Invalidate cache for a file (after edit)
me ctx.invalidate_file(file_path: text)
```

### Parsing

```simple
# Parse a file (cached)
me ctx.parse_file(file_path: text) -> Result<AST, ParseError>

# Parse source text (not cached)
fn ctx.parse_source_text(source: text, file_path: text) -> Result<AST, ParseError>
```

### Symbol Resolution

```simple
# Get symbol at a specific position
fn ctx.symbol_at(file_path: text, pos: Position) -> Option<Symbol>

# Find all references to a symbol
fn ctx.find_references(file_path: text, symbol: Symbol) -> [Location]

# Find definition of symbol at position
fn ctx.find_definition(file_path: text, pos: Position) -> Option<DefinitionResult>
```

### Type Information

```simple
# Get type at a position
fn ctx.type_at(file_path: text, pos: Position) -> Option<text>
```

### Completions

```simple
# Get completions at a position
fn ctx.completions_at(file_path: text, pos: Position) -> [Completion]
```

**Completion includes**:
- Variables in scope
- Functions in scope
- Keywords (context-aware)
- Imported modules
- Struct/enum members (in member access context)

### Hover Information

```simple
# Get hover information at a position
fn ctx.hover_at(file_path: text, pos: Position) -> Option<HoverInfo>
```

Returns markdown-formatted content with:
- Symbol name and type
- Documentation comments

### Diagnostics

```simple
# Get diagnostics for a file
me ctx.get_diagnostics(file_path: text) -> [Diagnostic]
```

Returns:
- Parse errors
- Type errors
- (Future: lint warnings)

### Document Symbols

```simple
# Get all symbols in a document (for outline view)
fn ctx.document_symbols(file_path: text) -> [Symbol]
```

### Workspace Symbols

```simple
# Search for symbols across the workspace
fn ctx.workspace_symbols(query: text) -> [Symbol]
```

## Data Types

### Symbol

```simple
struct Symbol:
    name: text
    kind: SymbolKind          # Variable, Function, Class, etc.
    location: Location
    type_info: Option<text>   # Human-readable type
    doc_comment: Option<text>
    is_public: bool
    is_mutable: bool
```

### Completion

```simple
struct Completion:
    label: text               # Display text
    kind: CompletionKind      # Variable, Function, Keyword, etc.
    detail: Option<text>      # Type signature
    documentation: Option<text>
    insert_text: text         # Text to insert
    sort_priority: i64        # Lower = higher priority
```

### Diagnostic

```simple
struct Diagnostic:
    range: Range
    severity: DiagnosticSeverity  # Error, Warning, Info, Hint
    message: text
    code: Option<text>            # Error code (e.g., "E0001")
    source: text                  # "simple-parser", "simple-type-checker"
```

### HoverInfo

```simple
struct HoverInfo:
    range: Range
    contents: text             # Markdown-formatted
    type_info: Option<text>
```

## Performance Considerations

### Incremental Parsing

The query context supports incremental parsing (future feature):

```simple
val ctx = CompilerQueryContext.create("/path/to/project")
ctx.incremental = true  # Enable incremental mode
```

When enabled, only changed portions of files are re-parsed.

### Cache Invalidation

Invalidate caches efficiently:

```simple
# Single file changed
ctx.invalidate_file("src/main.spl")

# Multiple files changed (batch)
for file in changed_files:
    ctx.invalidate_file(file)
```

### Response Time Targets

| Operation | Target | Notes |
|-----------|--------|-------|
| `completions_at` | < 50ms | Most common operation |
| `hover_at` | < 20ms | Must be instant |
| `get_diagnostics` | < 200ms | Can be async |
| `find_references` | < 500ms | Workspace-wide search |

## Integration with LSP

Example LSP server integration:

```simple
import compiler.query_api
import app.lsp.protocol

class SimpleLSPServer:
    query_ctx: CompilerQueryContext

    fn handle_completion_request(params: CompletionParams) -> [CompletionItem]:
        val pos = Position(line: params.position.line, column: params.position.character)
        val completions = self.query_ctx.completions_at(params.textDocument.uri, pos)

        # Convert to LSP format
        completions.map(\c: completion_to_lsp(c))

    fn handle_hover_request(params: HoverParams) -> Option<Hover>:
        val pos = Position(line: params.position.line, column: params.position.character)
        val hover = self.query_ctx.hover_at(params.textDocument.uri, pos)

        if not hover.?:
            return None

        val h = hover.unwrap()
        Some(Hover(
            contents: h.contents,
            range: range_to_lsp(h.range),
        ))
```

## FFI Integration

The query API relies on FFI functions implemented in Rust:

### Required FFI Functions

```simple
# Parser
extern fn parse_source(source: text, file_path: text) -> Result<AST, ParseError>

# Symbol resolution
extern fn build_symbol_table(ast: AST) -> SymbolTable
extern fn find_symbol_at_position(table: SymbolTable, pos: Position) -> Option<Symbol>
extern fn find_symbol_references(table: SymbolTable, name: text) -> [Location]
extern fn get_scope_at_position(table: SymbolTable, pos: Position) -> Scope

# Type checking
extern fn type_check_ast(ast: AST) -> [TypeError]

# Completions
extern fn get_context_keywords(pos: Position, scope: Scope) -> [text]

# Utilities
extern fn get_file_mtime(path: text) -> i64
```

### Implementation Location

These FFI functions should be implemented in:
- **Rust side**: `rust/compiler/src/query_ffi.rs` (new file)
- **SFFI spec**: `src/app/ffi_gen/specs/compiler_query.spl` (new file)

## Error Handling

The query API is designed to be resilient:

```simple
# Parse errors don't crash - return Result
val ast_result = ctx.parse_file("broken.spl")
if ast_result.err.?:
    val error = ast_result.err.unwrap()
    print "Parse error: {error.message}"

# Symbol not found - return None
val symbol = ctx.symbol_at("file.spl", Position(line: 10, column: 5))
if not symbol.?:
    print "No symbol at position"
```

### Partial AST Support (Future)

For better IDE experience, the parser should support error recovery:

```simple
# Parse with errors - return partial AST
val (ast, errors) = parse_source_with_recovery(source, file_path)

# Use partial AST for completions even if there are errors
val completions = ctx.completions_at_with_ast(ast, pos)
```

## Testing

### Unit Tests

```simple
# Test symbol resolution
describe "CompilerQueryContext":
    it "finds symbol at position":
        val source = """
        val x = 42
        val y = x + 1
        """

        val ctx = CompilerQueryContext.create(".")
        # ... write source to temp file ...
        val symbol = ctx.symbol_at("test.spl", Position(line: 1, column: 8))

        assert symbol.?.is_some()
        assert symbol.unwrap().name == "x"

    it "provides completions":
        val ctx = CompilerQueryContext.create(".")
        val completions = ctx.completions_at("test.spl", Position(line: 2, column: 0))

        assert completions.length > 0
        assert completions.any(\c: c.label == "val")
```

### Integration Tests

Test with real Simple projects:

```bash
# Run LSP integration tests
simple test test/integration/lsp/query_api_spec.spl
```

## Future Enhancements

### Incremental Compilation

- Parse only changed regions
- Incremental type checking
- Differential symbol table updates

### Workspace-Wide Analysis

- Global symbol index
- Cross-file references
- Module dependency graph

### Semantic Tokens

- Full semantic highlighting
- Token modifiers (declaration, definition, etc.)

### Code Actions

- Quick fixes for common errors
- Refactoring support
- Import organization

## Related Documentation

- **LSP Server**: `src/app/lsp/README.md`
- **Interpreter Hooks**: `doc/guide/interpreter_hooks_guide.md`
- **MCP Integration**: `doc/research/mcp_lsp_dap_integration_analysis.md`

## References

- LSP Specification: https://microsoft.github.io/language-server-protocol/
- Simple Compiler Architecture: `rust/compiler/`
- Parser Implementation: `rust/parser/`
