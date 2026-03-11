# T32 MCP Servers — TRACE32 Debug Session Control via MCP

Two MCP servers for TRACE32 tooling:

1. **MCP T32 LSP/DAP** — 26 tools: session management, window capture, CMM LSP, DAP validation
2. **MCP CMM CLI** — 8 tools: GUI-to-CLI conversion, bulk validation, headless execution

All T32 tools consolidated in `examples/10_tooling/t32_tool/`.

---

## Setup

### Claude Code

Add to `.mcp.json` in project root:

```json
{
  "mcpServers": {
    "simple-mcp-t32-lsp-dap": {
      "command": "bin/simple",
      "args": ["examples/10_tooling/t32_tool/mcp_lsp_dap/main.spl"]
    },
    "simple-mcp-cmm-cli": {
      "command": "bin/simple",
      "args": ["examples/10_tooling/t32_tool/mcp_cmm_cli/main.spl"]
    }
  }
}
```

### Claude Desktop

Add to Claude Desktop config (`~/.config/Claude/claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "simple-mcp-t32-lsp-dap": {
      "command": "/path/to/simple/bin/simple",
      "args": ["examples/10_tooling/t32_tool/mcp_lsp_dap/main.spl"],
      "env": {
        "SIMPLE_PROJECT_ROOT": "/path/to/simple"
      }
    },
    "simple-mcp-cmm-cli": {
      "command": "/path/to/simple/bin/simple",
      "args": ["examples/10_tooling/t32_tool/mcp_cmm_cli/main.spl"],
      "env": {
        "SIMPLE_PROJECT_ROOT": "/path/to/simple"
      }
    }
  }
}
```

### Verify

```bash
# Test MCP T32 LSP/DAP
echo '{"jsonrpc":"2.0","id":"1","method":"tools/list"}' | bin/simple examples/10_tooling/t32_tool/mcp_lsp_dap/main.spl

# Test MCP CMM CLI
echo '{"jsonrpc":"2.0","id":"1","method":"tools/list"}' | bin/simple examples/10_tooling/t32_tool/mcp_cmm_cli/main.spl
```

---

## Protocol

- **MCP Version:** 2025-06-18
- **Framing:** Content-Length + JSON-Lines auto-detect
- **Transport:** stdio (JSON-RPC 2.0)
- **Tools:** 26 (MCP T32 LSP/DAP) + 8 (MCP CMM CLI) = 34 total

---

## Tool Reference — MCP T32 LSP/DAP

### Session Tools (9)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `t32_sessions_list` | List all TRACE32 sessions | |
| `t32_session_open` | Open new session (connect to PowerView) | host, port |
| `t32_session_resume` | Resume/switch to existing session | session_id |
| `t32_session_close` | Close session | session_id |
| `t32_core_list` | List cores in current session | |
| `t32_core_select` | Select active core | core_id |
| `t32_cmd_run` | Run raw PRACTICE command | command |
| `t32_cmm_run` | Run CMM script | script |
| `t32_eval` | Evaluate TRACE32 expression | expression |

### Window Tools (5)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `t32_window_list` | List available windows from catalog | |
| `t32_window_open` | Open a TRACE32 window | window |
| `t32_window_capture` | Capture window content as text | window |
| `t32_window_describe` | Describe window actions and fields | window |
| `t32_screenshot` | Take screenshot of window | window |

### Action/Field Tools (6)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `t32_action_invoke` | Invoke a window action | action_key |
| `t32_field_get` | Get field value from session state | field_key |
| `t32_field_set` | Set field value | field_key, value |
| `t32_history_tail` | Get recent command history | |
| `t32_resources_list` | List available T32 MCP resources | |
| `t32_resource_read` | Read a specific resource by URI | uri |

### Tool Annotations

| Annotation | Tools |
|-----------|-------|
| Read-only | `t32_sessions_list`, `t32_core_list`, `t32_window_list`, `t32_window_capture`, `t32_window_describe`, `t32_field_get`, `t32_history_tail`, `t32_eval`, `t32_resources_list`, `t32_resource_read` |
| Destructive | `t32_session_close` |
| Non-idempotent | `t32_cmd_run`, `t32_cmm_run`, `t32_action_invoke` |

### CMM LSP Tools (6) — NEW

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `cmm_parse` | Parse CMM file, return AST summary | path or source |
| `cmm_lint` | Analyze CMM for errors/warnings | path or source |
| `cmm_hover` | Get command/function documentation | name |
| `cmm_complete` | Auto-complete commands/functions | prefix |
| `cmm_goto_def` | Find label/macro definition | name, path or source |
| `cmm_symbols` | List all symbols in CMM file | path or source |

### DAP Validation Tools (1) — NEW

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `cmm_validate_before_run` | Pre-execution lint for DO command | path or source |

---

## Tool Reference — MCP CMM CLI

### Converter Tools (3)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `cmm_convert_file` | Convert single CMM from GUI to CLI | path |
| `cmm_convert_dir` | Bulk convert directory | input_dir |
| `cmm_preview` | Preview conversion without writing | path |

### Validator Tools (3)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `cmm_bulk_validate` | Validate all CMM files in directory | dir |
| `cmm_check_gui` | Check file for GUI-only commands | path |
| `cmm_report` | GUI command usage statistics | dir |

### Runner Tools (2)

| Tool | Description | Required Params |
|------|-------------|-----------------|
| `cmm_run_converted` | Convert and prepare for execution | path |
| `cmm_diff_original` | Show diff between original and converted | path |

---

## Example Workflow

```
1. t32_session_open(host: "localhost", port: "20000", name: "stm32wb", architecture: "ARM")
2. t32_core_list()
3. t32_core_select(core_id: "core0")
4. t32_cmd_run(command: "SYStem.Up")
5. t32_window_capture(window: "register_view")
6. t32_action_invoke(action_key: "set_break", args: "main")
7. t32_cmd_run(command: "Go")
8. t32_window_capture(window: "var_local")
9. t32_screenshot(window: "source_list", output_path: "debug_session.png")
10. t32_history_tail(count: "10")
11. t32_session_close(session_id: "s1")
```

---

## Architecture

```
examples/10_tooling/t32_tool/
  cmm/              CMM language core (AST, lexer, parser, analyzer)
  lsp/              CMM LSP server (completion, hover, goto-def)
  converter/        GUI-to-CLI converter (strip/transform/keep)
  mcp_lsp_dap/      MCP 1: T32 session + CMM LSP + DAP validation
  mcp_cmm_cli/      MCP 2: Converter + validator + runner
  cli/              T32 CLI (session/window/action management)
  shared/           Shared: JSON helpers, protocol, session types, t32rem
  validate/         Validation scripts and test runners
  test_fixtures/    CMM test files (riscv/, web/)
  mod.spl           Unified entry point
```

Communication with TRACE32 uses `t32rem` (Remote API CLI). The MCP servers manage session state, dispatch commands, and return structured results.

---

## Relationship to Other Guides

- **Host setup:** [backend/trace32_linux_setup.md](../backend/trace32_linux_setup.md) — udev rules, probe access, PowerView startup
- **Docker experiment:** [backend/trace32_docker_experiment.md](../backend/trace32_docker_experiment.md) — containerized T32 testing
- **CLI tool:** [tools/t32_cli.md](t32_cli.md) — command-line equivalent (same catalogs, same protocol layer)
- **Main MCP server:** [tooling/mcp.md](../tooling/mcp.md) — the primary Simple MCP server (66 tools, separate from T32 MCP)

---

## Source Code

- **Unified T32 tooling:** `examples/10_tooling/t32_tool/` (51 .spl files, ~15K lines)
- **MCP T32 LSP/DAP:** `examples/10_tooling/t32_tool/mcp_lsp_dap/` (8 files)
- **MCP CMM CLI:** `examples/10_tooling/t32_tool/mcp_cmm_cli/` (4 files)
- **CMM parser/LSP:** `examples/10_tooling/t32_tool/cmm/` + `lsp/` (19 files)
- **GUI-to-CLI converter:** `examples/10_tooling/t32_tool/converter/` (4 files)
- **T32 CLI:** `examples/10_tooling/t32_tool/cli/` (9 files)
- **Shared utilities:** `examples/10_tooling/t32_tool/shared/` (4 files)
- **Protocol layer:** `src/lib/nogc_sync_mut/debug/remote/protocol/`
- **Catalogs:** `config/t32/catalogs/` (windows, actions, fields in SDN)
- **Tests:** `test/unit/app/mcp_t32/` (dispatch + JSON specs)

### Legacy locations (originals preserved)

- `src/app/mcp_t32/` — original monolithic MCP server
- `src/app/t32_cli/` — original CLI tool
- `examples/10_tooling/cmm_lsp/` — original CMM LSP
