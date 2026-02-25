# Simple MCP Server - Usage Guide

## Installation in Claude Code

**Configuration:** `.mcp.json` (project root, git-tracked)

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "bin/simple_mcp_server",
      "args": []
    }
  }
}
```

## Available Tools (66 total)

### Debug Session Tools (19)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `debug_create_session` | Create debug session | program | target_type |
| `debug_list_sessions` | List active sessions | | |
| `debug_close_session` | Close session | session_id | |
| `debug_set_breakpoint` | Set breakpoint | session_id, file, line | condition |
| `debug_remove_breakpoint` | Remove breakpoint | session_id, breakpoint_id | |
| `debug_continue` | Continue execution | session_id | |
| `debug_step` | Step through code | session_id, mode | |
| `debug_get_variables` | Get variables | session_id | |
| `debug_stack_trace` | Get stack trace | session_id | |
| `debug_evaluate` | Evaluate expression | session_id, expression | |
| `debug_set_function_breakpoint` | Set function breakpoint | session_id, function_name | |
| `debug_enable_breakpoint` | Enable/disable breakpoint | session_id, breakpoint_id, enabled | |
| `debug_get_source` | Get source code | session_id, file | start_line, count |
| `debug_watch` | Add watch expression | session_id, action | expression |
| `debug_set_variable` | Set variable value | session_id, name, value | frame_index |
| `debug_set_data_breakpoint` | Set data breakpoint | session_id, name | access_type, condition |
| `debug_list_data_breakpoints` | List data breakpoints | session_id | |
| `debug_remove_data_breakpoint` | Remove data breakpoint | session_id, breakpoint_id | |
| `debug_terminate` | Terminate session | session_id | |

### Debug Log Tools (6)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `debug_log_enable` | Enable debug logging | | pattern |
| `debug_log_disable` | Disable debug logging | | |
| `debug_log_clear` | Clear debug logs | | |
| `debug_log_query` | Query debug logs | | since_id, entry_type, max_results, function_pattern |
| `debug_log_tree` | Get debug log tree | | format, max_depth, since_id, expanded_groups |
| `debug_log_status` | Get debug log status | | |

### Diagnostic Tools (7)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_read` | Read source with diagnostics | path | show_hints, fold_mode |
| `simple_check` | Check for errors | path | |
| `simple_symbols` | List symbols in file | path | |
| `simple_status` | Get project status | | directory, paths |
| `simple_edit` | Edit source file | path, old_string, new_string | |
| `simple_multi_edit` | Edit multiple files | path, edits | |
| `simple_run` | Run Simple code | path | |

### VCS Tools (4)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_diff` | Show file diff | | revision, paths |
| `simple_log` | Show git log | | limit, revsets |
| `simple_squash` | Squash commits | | revision, message |
| `simple_new` | Create new change | | revision, message |

### API Search (1)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_api` | Module API with visibility filtering | | module, query, visibility |

### CLI Tools — Tier 1 (6)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_test` | Run tests | | path, filter, only_slow, list |
| `simple_build` | Build project | | release, target, warn_docs |
| `simple_format` | Format file/project | | path, check |
| `simple_lint` | Lint with output | | path |
| `simple_fix` | Auto-fix issues | path | dry_run |
| `simple_doc_coverage` | Doc coverage report | | format, missing |

### Query Tools — Tier 2 (5)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_definition` | Go-to-definition | file, line | column |
| `simple_references` | Find all references | file, line | column |
| `simple_hover` | Type + docs at position | file, line | column |
| `simple_completions` | Code completions | file, line | column, prefix |
| `simple_type_at` | Type info at position | file, line | column |

### Analysis Tools — Tier 3 (4)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_dependencies` | Module dependency graph | | file, depth, format |
| `simple_api_diff` | API surface diff | file | revision |
| `simple_context` | Context pack for AI/docs | file | target |
| `simple_search` | Language-aware code search | query | kind, scope, file |

### LSP Tools — Tier 4 (10)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_signature_help` | Parameter hints at call site | file, line | column |
| `simple_rename` | Rename symbol across project | file, line, new_name | column |
| `simple_code_actions` | Quick fixes at position | file, line | column |
| `simple_workspace_symbols` | Search symbols across project | query | kind |
| `simple_call_hierarchy` | Incoming/outgoing call chains | file, line | column, direction |
| `simple_type_hierarchy` | Super/sub type relationships | file, line | column, direction |
| `simple_semantic_tokens` | Semantic highlighting data | file | start_line, end_line |
| `simple_inlay_hints` | Inline type/param annotations | file | start_line, end_line |
| `simple_selection_range` | Smart selection expand/shrink | file, line | column |
| `simple_document_formatting` | Format a document | file | options |

### LSP Extra Tools (4)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_document_highlight` | Same-file references (R/W) | file, line | column |
| `simple_type_definition` | Find where type is defined | file, line | column |
| `simple_implementation` | Find trait implementations | file, line | column |
| `simple_folding_range` | Get folding ranges | file | |

### Code Query Tools (3)

| Tool | Description | Required | Optional |
|------|-------------|----------|----------|
| `simple_ast_query` | S-expression structural pattern matching | query | files, format |
| `simple_sem_query` | CodeQL-style semantic query (SQL-like) | query | files, format |
| `simple_query_schema` | List available query node types | | kind |

**AST Query examples:**
```bash
bin/simple query ast-query '(function name: "main")'
bin/simple query ast-query '(struct)' --files src/app/cli/ --format json
bin/simple query ast-query '(class methods: (function name: "to_string"))'
```

**Semantic Query examples:**
```bash
bin/simple query sem-query 'FIND fn WHERE return_type = "i64"'
bin/simple query sem-query 'FIND fn WHERE name starts_with "parse_" AND param_count > 2'
bin/simple query sem-query 'FIND fn WHERE calls("rt_file_read_text")'
bin/simple query sem-query 'FIND struct WHERE field_count > 3'
```

**Schema discovery:**
```bash
bin/simple query query-schema         # Both AST + Semantic
bin/simple query query-schema ast     # AST schema only
bin/simple query query-schema sem     # Semantic schema only
```

## Server Features

- **Protocol:** JSON-RPC 2.0 over stdio (auto-detects Content-Length or JSON-lines)
- **MCP Version:** 2025-06-18
- **Server:** simple-mcp-full v4.0.0
- **Startup:** ~100ms (zero imports, all inline)
- **Capabilities:** Tools, Resources, Prompts, Logging, Completions, Roots
- **Tool Annotations:** readOnlyHint, destructiveHint, idempotentHint, openWorldHint

## Testing

```bash
# List tools
echo '{"jsonrpc":"2.0","id":"2","method":"tools/list"}' | bin/simple_mcp_server

# Call a tool
echo '{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"simple_read","arguments":{"path":"src/app/cli/query.spl"}}}' | bin/simple_mcp_server
```
