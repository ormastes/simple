# MCP LSP Tools (Tier 4)

**Feature IDs:** #500-510
**Status:** Implemented
**Since:** v4.0.0

## Overview

10 LSP tools + 4 LSP extras + 3 code query tools added to the Simple MCP server, bringing the total to 66 tools. These tools provide IDE-grade code intelligence for Simple Language source files.

## Tools

### Navigation & Information

| Tool | Description | Required Params | Optional Params |
|------|-------------|----------------|-----------------|
| `simple_signature_help` | Function parameter hints at call site | file, line | column |
| `simple_workspace_symbols` | Search symbols across project | query | kind |
| `simple_selection_range` | Smart selection expand/shrink | file, line | column |

### Refactoring

| Tool | Description | Required Params | Optional Params |
|------|-------------|----------------|-----------------|
| `simple_rename` | Rename symbol across project | file, line, new_name | column |
| `simple_code_actions` | Quick fixes at position | file, line | column |
| `simple_document_formatting` | Format source file | file | options |

### Code Intelligence

| Tool | Description | Required Params | Optional Params |
|------|-------------|----------------|-----------------|
| `simple_call_hierarchy` | Incoming/outgoing call chains | file, line | column, direction |
| `simple_type_hierarchy` | Trait impl relationships | file, line | column, direction |
| `simple_semantic_tokens` | Semantic highlighting data | file | start_line, end_line |
| `simple_inlay_hints` | Inline type/param annotations | file | start_line, end_line |

## Architecture

All tools use the CLI bridge pattern:
1. MCP handler extracts parameters from JSON-RPC
2. Delegates to `bin/simple query <subcommand>` via shell
3. Returns structured text output

## Usage Examples

```bash
# Signature help at position
bin/simple query signature-help src/app/cli/query.spl 17

# Rename symbol
bin/simple query rename src/app/cli/query.spl 17 --new-name new_name

# Search workspace symbols
bin/simple query workspace-symbols --query parse --kind fn

# Call hierarchy
bin/simple query call-hierarchy src/app/cli/query.spl 17 --direction incoming

# Semantic tokens for a range
bin/simple query semantic-tokens src/app/cli/query.spl --start-line 1 --end-line 50

# Inlay hints
bin/simple query inlay-hints src/app/cli/query.spl

# Format document
bin/simple query document-formatting src/app/cli/query.spl
```

## Annotations

| Tool | Read-Only | Destructive | Idempotent |
|------|-----------|-------------|------------|
| `simple_signature_help` | Yes | No | Yes |
| `simple_rename` | No | **Yes** | No |
| `simple_code_actions` | Yes | No | Yes |
| `simple_workspace_symbols` | Yes | No | Yes |
| `simple_call_hierarchy` | Yes | No | Yes |
| `simple_type_hierarchy` | Yes | No | Yes |
| `simple_semantic_tokens` | Yes | No | Yes |
| `simple_inlay_hints` | Yes | No | Yes |
| `simple_selection_range` | Yes | No | Yes |
| `simple_document_formatting` | No | **Yes** | No |

## Code Query Tools (3)

3 new code query tools providing CodeQL-style structural and semantic queries against the codebase.

### Structural Pattern Matching

| Tool | Description | Required Params | Optional Params |
|------|-------------|----------------|-----------------|
| `simple_ast_query` | S-expression structural pattern matching | query | files, format |
| `simple_sem_query` | CodeQL-style semantic query (SQL-like) | query | files, format |
| `simple_query_schema` | List available node types and predicates | | kind |

### AST Query Syntax (S-expression)

```
(function name: "main")
(function return_type: "i64" visibility: "pub")
(class methods: (function name: "to_string"))
(struct fields: (field type: "i64"))
(import module: "std.*")
(impl trait: "Printable")
(* name: "query_main")
```

Node kinds: `function`, `class`, `struct`, `enum`, `trait`, `impl`, `import`, `field`, `val`, `var`, `*`
Predicates: `name`, `return_type`, `params`, `type`, `module`, `parent`, `kind`, `signature`, `trait`, `visibility`

### Semantic Query Syntax (SQL-like)

```
FIND fn WHERE return_type = "i64"
FIND fn WHERE name starts_with "parse_" AND param_count > 2
FIND fn WHERE calls("rt_file_read_text")
FIND class WHERE has_method("to_string")
FIND struct WHERE field_count > 5
FIND import WHERE module contains "std"
FIND impl WHERE trait = "Iterator"
```

Targets: `fn`, `class`, `struct`, `enum`, `trait`, `impl`, `import`, `type`, `field`, `val`, `var`, `*`
Operators: `=`, `!=`, `>`, `<`, `>=`, `<=`, `starts_with`, `ends_with`, `contains`
Functions: `calls("name")`, `has_method("name")`, `implements("name")`, `imports("name")`
Numeric fields: `param_count`, `field_count`

### Code Query Usage Examples

```bash
# AST pattern queries
bin/simple query ast-query '(function name: "query_main")'
bin/simple query ast-query '(function return_type: "i64")' --files src/app/cli/
bin/simple query ast-query '(class methods: (function name: "to_string"))' --files src/lib/
bin/simple query ast-query '(struct)' --format json --files src/compiler/

# Semantic queries
bin/simple query sem-query 'FIND fn WHERE return_type = "i64"' --files src/app/cli/query.spl
bin/simple query sem-query 'FIND fn WHERE name starts_with "engine_"' --files src/app/cli/
bin/simple query sem-query 'FIND fn WHERE calls("rt_file_read_text")' --files src/app/cli/
bin/simple query sem-query 'FIND struct WHERE field_count > 3'

# Schema discovery
bin/simple query query-schema
bin/simple query query-schema ast
bin/simple query query-schema sem
```

### Code Query Annotations

| Tool | Read-Only | Destructive | Idempotent |
|------|-----------|-------------|------------|
| `simple_ast_query` | Yes | No | Yes |
| `simple_sem_query` | Yes | No | Yes |
| `simple_query_schema` | Yes | No | Yes |

## Compiler Query API

The typed API in `src/compiler/90.tools/query_api.spl` defines interfaces for all features. Currently uses `pass_todo` stubs -- will be connected to FFI when the compiler backend supports these queries directly.

### New Types Added
- `SignatureHelp`, `SignatureInfo`, `ParameterInfo`
- `CallHierarchyItem`, `CallHierarchyIncomingCall`, `CallHierarchyOutgoingCall`
- `TypeHierarchyItem`
- `SemanticTokenType` (enum), `SemanticToken`
- `InlayHintKind` (enum), `InlayHint`
- `SelectionRangeEntry`
- `RenameEdit`, `WorkspaceEdit`
- `CodeAction`

## Tests

### Code Query Tests (232 tests total)

| Test File | Tests | Type |
|-----------|-------|------|
| `test/unit/app/cli/query_ast_query_spec.spl` | 25 | Unit — pattern parsing, predicate eval |
| `test/unit/app/cli/query_sem_query_spec.spl` | 34 | Unit — query parsing, field matching |
| `test/unit/app/cli/query_schema_spec.spl` | 6 | Unit — schema content |
| `test/unit/app/cli/query_ast_query_integration_spec.spl` | 21 | Integration — full CLI pipeline |
| `test/unit/app/cli/query_sem_query_integration_spec.spl` | 32 | Integration — full CLI pipeline |
| `test/unit/app/cli/query_engine_spec.spl` | 51 | Unit — outline parser engine |
| `test/unit/app/cli/query_upgrade_spec.spl` | 33 | Unit — query upgrade helpers |
| `test/unit/app/cli/query_sanitize_spec.spl` | 30 | Unit — input sanitization |

## Related

- [MCP Server](../../src/lib/nogc_sync_mut/mcp/main_lazy.spl) -- Server entry point
- [Query CLI](../../src/app/cli/query.spl) -- CLI subcommands
- [AST Query Engine](../../src/app/cli/query_ast_query.spl) -- S-expression pattern matching
- [Semantic Query Engine](../../src/app/cli/query_sem_query.spl) -- SQL-like semantic queries
- [Query Schema](../../src/app/cli/query_schema.spl) -- Schema discovery
- [Query API](../../src/compiler/90.tools/query_api.spl) -- Typed compiler API
- [LSP Emitter](../../src/lib/common/report/emitter/lsp.spl) -- LSP format types
