# MCP Server Setup and Usage

The Simple MCP (Model Context Protocol) server currently provides 108 tools, 3
resources, and 2 prompts for code intelligence, debugging, build, VCS,
analysis, and UI access -- accessible from Claude Code and Claude Desktop.

---

## Setup

### Claude Code

The MCP server is configured via `.mcp.json` in the project root (auto-detected by Claude Code).

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

Install platform-specific config automatically:

```bash
sh config/mcp/install.shs
```

### Claude Desktop

Configure in the Claude Desktop config file:
- **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
- **Linux**: `~/.config/Claude/claude_desktop_config.json`

```json
{
  "mcpServers": {
    "simple-lang": {
      "command": "/path/to/simple/bin/simple_mcp_server",
      "args": [],
      "env": {
        "SIMPLE_PROJECT_ROOT": "/path/to/simple"
      }
    }
  }
}
```

Restart Claude Desktop after config changes.

### Verify Installation

```bash
# Test server startup
echo '{"jsonrpc":"2.0","id":"2","method":"tools/list"}' | bin/simple_mcp_server

# Run integration tests
SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
```

---

## Architecture

```
Claude Code / Claude Desktop
    | JSON-RPC 2.0 over stdio
    v
bin/simple_mcp_server
    |-> Tool handlers (lazy loaded)
    |-> Bug/Feature/Test DB resources
    |-> Debug session manager
```

- **Protocol**: JSON-RPC 2.0 over stdio
- **MCP Version**: 2025-06-18
- **Startup**: < 1s (optimized single-process)
- **Tool count**: 108 tools

---

## Tool Reference

### Debug Session (19 tools)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `debug_create_session` | Create debug session | program |
| `debug_list_sessions` | List active sessions | |
| `debug_close_session` | Close session | session_id |
| `debug_set_breakpoint` | Set breakpoint | session_id, file, line |
| `debug_remove_breakpoint` | Remove breakpoint | session_id, breakpoint_id |
| `debug_continue` | Continue execution | session_id |
| `debug_step` | Step through code | session_id, mode |
| `debug_get_variables` | Get variables | session_id |
| `debug_stack_trace` | Get stack trace | session_id |
| `debug_evaluate` | Evaluate expression | session_id, expression |
| `debug_set_function_breakpoint` | Function breakpoint | session_id, function_name |
| `debug_enable_breakpoint` | Enable/disable | session_id, breakpoint_id, enabled |
| `debug_get_source` | Get source code | session_id, file |
| `debug_watch` | Watch expression | session_id, action |
| `debug_set_variable` | Set variable value | session_id, name, value |
| `debug_set_data_breakpoint` | Data breakpoint | session_id, name |
| `debug_list_data_breakpoints` | List data breakpoints | session_id |
| `debug_remove_data_breakpoint` | Remove data breakpoint | session_id, breakpoint_id |
| `debug_terminate` | Terminate session | session_id |

### Debug Logging (6 tools)

| Tool | Description |
|------|-------------|
| `debug_log_enable` | Enable logging (optional: pattern) |
| `debug_log_disable` | Disable logging |
| `debug_log_clear` | Clear logs |
| `debug_log_query` | Query logs (filter by type, function, etc.) |
| `debug_log_tree` | Log tree view |
| `debug_log_status` | Logging status |

### Diagnostics (7 tools)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `simple_read` | Read with diagnostics | path |
| `simple_check` | Syntax/type check | path |
| `simple_symbols` | List symbols | path |
| `simple_status` | Project status | |
| `simple_edit` | Edit file | path, old_string, new_string |
| `simple_multi_edit` | Batch edit | path, edits |
| `simple_run` | Run Simple code | path |

### VCS (4 tools)

| Tool | Description |
|------|-------------|
| `simple_diff` | Show diff (optional: revision, paths) |
| `simple_log` | Commit history (optional: limit, revsets) |
| `simple_squash` | Squash commits |
| `simple_new` | Create change |

### CLI (6 tools)

| Tool | Description |
|------|-------------|
| `simple_test` | Run tests (optional: path, filter) |
| `simple_build` | Build project (optional: release, target) |
| `simple_format` | Format code |
| `simple_lint` | Lint code |
| `simple_fix` | Auto-fix issues (required: path) |
| `simple_doc_coverage` | Doc coverage report |

### Query (5 tools)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `simple_definition` | Go-to-definition | file, line |
| `simple_references` | Find references | file, line |
| `simple_hover` | Type + docs | file, line |
| `simple_completions` | Completions | file, line |
| `simple_type_at` | Type at position | file, line |

### Analysis (5 tools)

| Tool | Description |
|------|-------------|
| `simple_api` | Module API (optional: module, query, visibility) |
| `simple_dependencies` | Dependency graph |
| `simple_api_diff` | API surface diff (required: file) |
| `simple_context` | Context pack (required: file) |
| `simple_search` | Code search (required: query) |

### UI Access (11 tools)

These tools expose the canonical semantic UI model over active `UISession`
surfaces.

| Tool | Description |
|------|-------------|
| `ui_access_snapshot` | Read the canonical UI access snapshot |
| `ui_access_surface` | Read one named UI surface and its nodes |
| `ui_access_find` | Find canonical nodes by surface, kind, text, or focus |
| `ui_access_act` | Dispatch an action against a canonical UI node |
| `ui_access_history` | Read recent UI access events |
| `ui_access_observe` | Read the narrowest canonical view for a surface, node, or filtered query |
| `ui_access_state` | Read or set constrained declarative surface/node state over the canonical protocol |
| `ui_access_value` | Read or write typed values for canonical `input`, `textfield`, and `textarea` nodes |
| `ui_access_query` | Query canonical UI nodes with structured JSON results |
| `ui_access_adapter_snapshot` | Read additive source/target metadata around a canonical snapshot |
| `ui_access_visual_probe` | Read semantic marks and issues from the vision sidecar |

For the operator workflow and HTTP route equivalents, see
[tooling/ui_access.md](ui_access.md).

### LSP (14 tools)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `simple_signature_help` | Parameter hints | file, line |
| `simple_rename` | Rename symbol | file, line, new_name |
| `simple_code_actions` | Quick fixes | file, line |
| `simple_workspace_symbols` | Search symbols | query |
| `simple_call_hierarchy` | Call chains | file, line |
| `simple_type_hierarchy` | Type tree | file, line |
| `simple_semantic_tokens` | Semantic tokens | file |
| `simple_inlay_hints` | Inlay annotations | file |
| `simple_selection_range` | Smart selection | file, line |
| `simple_document_formatting` | Format document | file |
| `simple_document_highlight` | Same-file refs | file, line |
| `simple_type_definition` | Type definition | file, line |
| `simple_implementation` | Trait impls | file, line |
| `simple_folding_range` | Folding ranges | file |

### Code Query (3 tools)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `simple_ast_query` | Structural pattern match | query |
| `simple_sem_query` | Semantic query (SQL-like) | query |
| `simple_query_schema` | Query node types | |

**AST Query examples:**
```bash
bin/simple query ast-query '(function name: "main")'
bin/simple query ast-query '(struct)' --files src/app/cli/ --format json
```

**Semantic Query examples:**
```bash
bin/simple query sem-query 'FIND fn WHERE return_type = "i64"'
bin/simple query sem-query 'FIND fn WHERE name starts_with "parse_" AND param_count > 2'
```

---

## Resources (URIs)

| URI | Description |
|-----|-------------|
| `file:///{path}` | File contents |
| `symbol:///{name}` | Symbol info |
| `type:///{name}` | Type info |
| `tree:///{path}` | Directory tree |
| `bugdb://all` | All bugs |
| `bugdb://open` | Open bugs |
| `bugdb://critical` | P0/P1 bugs |
| `bugdb://bug/{id}` | Single bug |
| `bugdb://stats` | Bug statistics |

---

## Extending the Server

### Add a New Tool

1. Add handler in `src/app/mcp/bootstrap/main_optimized.spl`:
   ```simple
   fn handle_my_tool(params: Dict) -> Result<text, text>:
       val path = params.get("path")?
       Ok("result")
   ```

2. Register schema in `src/app/mcp/mcp_lib/schema.spl`

3. Rebuild: `bin/simple build src/app/mcp/bootstrap/main_optimized.spl`

---

## Troubleshooting

**Server not found:**
- Verify `.mcp.json` exists with valid JSON: `python3 -m json.tool .mcp.json`
- Check binary is executable: `ls -la bin/simple_mcp_server`
- Restart Claude Desktop / Claude Code

**Tools not working:**
- Check `SIMPLE_PROJECT_ROOT` env var is set correctly
- Check logs: `~/Library/Logs/Claude/` (macOS) or `~/.config/Claude/logs/` (Linux)

---

## Source Code

- **MCP server**: `src/app/mcp/`
- **Config installer**: `config/mcp/install.shs`
- **Tests**: `test/integration/app/mcp_*_spec.spl`
