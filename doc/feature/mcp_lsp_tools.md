# MCP LSP Tools (Tier 4)

**Feature IDs:** #500-510
**Status:** Implemented
**Since:** v4.0.0

## Overview

10 new Language Server Protocol (LSP) compatible tools added to the Simple MCP server, bringing the total from 49 to 59 tools. These tools provide IDE-grade code intelligence for Simple Language source files.

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

## Related

- [MCP Server](../../src/lib/nogc_sync_mut/mcp/main_lazy.spl) -- Server entry point
- [Query CLI](../../src/app/cli/query.spl) -- CLI subcommands
- [Query API](../../src/compiler/90.tools/query_api.spl) -- Typed compiler API
- [LSP Emitter](../../src/lib/common/report/emitter/lsp.spl) -- LSP format types
