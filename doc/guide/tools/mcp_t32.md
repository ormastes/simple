# T32 MCP Server — TRACE32 Debug Session Control via MCP

MCP server exposing 20 tools for TRACE32 debug session management, window capture, action invocation, and field manipulation. Enables AI assistants (Claude Code, Claude Desktop) to control TRACE32 debug sessions.

---

## Setup

### Claude Code

Add to `.mcp.json` in project root:

```json
{
  "mcpServers": {
    "simple-mcp-t32": {
      "command": "bin/simple",
      "args": ["mcp-t32"]
    }
  }
}
```

### Claude Desktop

Add to Claude Desktop config (`~/.config/Claude/claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "simple-mcp-t32": {
      "command": "/path/to/simple/bin/simple",
      "args": ["mcp-t32"],
      "env": {
        "SIMPLE_PROJECT_ROOT": "/path/to/simple"
      }
    }
  }
}
```

### Verify

```bash
echo '{"jsonrpc":"2.0","id":"1","method":"tools/list"}' | bin/simple mcp-t32
```

---

## Protocol

- **MCP Version:** 2025-06-18
- **Framing:** Content-Length + JSON-Lines auto-detect
- **Transport:** stdio (JSON-RPC 2.0)
- **Tools:** 20

---

## Tool Reference

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
Claude Code / Claude Desktop
    | JSON-RPC 2.0 over stdio
    v
bin/simple mcp-t32
    |-> protocol.spl       — I/O framing, initialize, tools list, schemas
    |-> session_tools.spl   — Session/core/command handlers
    |-> window_tools.spl    — Window list/open/capture/describe/screenshot
    |-> action_tools.spl    — Action invoke, field get/set, history, resources
    |-> json_helpers.spl    — JSON builders, shell wrappers
    |-> main.spl            — Entry point, message routing, state
```

Communication with TRACE32 uses `t32rem` (Remote API CLI). The MCP server manages session state, dispatches commands, and returns structured results.

---

## Relationship to Other Guides

- **Host setup:** [backend/trace32_linux_setup.md](../backend/trace32_linux_setup.md) — udev rules, probe access, PowerView startup
- **Docker experiment:** [backend/trace32_docker_experiment.md](../backend/trace32_docker_experiment.md) — containerized T32 testing
- **CLI tool:** [tools/t32_cli.md](t32_cli.md) — command-line equivalent (same catalogs, same protocol layer)
- **Main MCP server:** [tooling/mcp.md](../tooling/mcp.md) — the primary Simple MCP server (66 tools, separate from T32 MCP)

---

## Source Code

- **MCP server:** `src/app/mcp_t32/` (6 files)
- **Protocol layer:** `src/lib/nogc_sync_mut/debug/remote/protocol/`
- **Catalogs:** `config/t32/catalogs/` (windows, actions, fields in SDN)
- **Tests:** `test/unit/app/mcp_t32/` (dispatch + JSON specs)
