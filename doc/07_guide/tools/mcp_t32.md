# T32 MCP Guide

The TRACE32 MCP server lives in `examples/10_tooling/trace32_tools/t32_mcp/` and exposes 35 tools for live TRACE32 session control. The paired CMM analysis server lives in `examples/10_tooling/trace32_tools/t32_lsp_mcp/`.

## Canonical Paths

- T32 MCP: `examples/10_tooling/trace32_tools/t32_mcp/main.spl`
- T32 LSP MCP: `examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl`
- Window catalog: `config/t32/catalogs/windows.sdn`
- MCP config: `config/t32/t32_mcp.sdn`

## Setup

Enable the TRACE32 Remote API in PowerView with `RCL.Port 20000` or a matching `RCL=NETASSIST` configuration, then add the MCP server:

```bash
claude mcp add t32-mcp -- \
  /absolute/path/to/simple/bin/release/simple \
  /absolute/path/to/simple/examples/10_tooling/trace32_tools/t32_mcp/main.spl
```

The server uses `config/t32/t32_mcp.sdn` for defaults:

```sdn
connection
  default_port: 20000
  default_host: localhost
  rcl_port: 20000
  rcl_host: localhost
  backend_preference: t32rem
  python_binary: python3
  python_bridge:
  api_lib_path:
```

Override order:
1. CLI flags such as `--host=` and `--port=`
2. Environment variables (see table below)
3. `config/t32/t32_mcp.sdn`

| Environment Variable | SDN Key | Description |
|---------------------|---------|-------------|
| `T32_DEFAULT_HOST` | `default_host` | TRACE32 host address |
| `T32_DEFAULT_PORT` | `default_port` | TRACE32 port number |
| `T32_RCL_HOST` | `rcl_host` | RCL host (fallback for default) |
| `T32_RCL_PORT` | `rcl_port` | RCL port (fallback for default) |
| `T32_BACKEND_PREFERENCE` | `backend_preference` | Backend: `ctypes`, `t32rem`, or `python_rcl` |
| `T32_PYTHON` | `python_binary` | Python binary path (default: `python3`) |
| `T32_PYTHON_BRIDGE` | `python_bridge` | Path to `t32_python_bridge.py` |
| `T32_API_LIB` | `api_lib_path` | Path to `t32api64.so` for ctypes backend |

## Backends

The server supports three backends, tried in priority order:

| Priority | Backend | Type | Description |
|----------|---------|------|-------------|
| 1 | `ctypes` | In-process | Loads `t32api64.so` via DynLib. Persistent connection, zero subprocess overhead. Requires compiled binary mode. |
| 2 | `t32rem` | Subprocess | Lauterbach CLI tool. One process per command. |
| 3 | `python_rcl` | Subprocess | Python bridge using `lauterbach.trace32.rcl`. One process per command. |

Set `backend_preference` to force a specific backend. When empty, the server tries ctypes first (if `t32api64.so` is available), then `t32rem`, then `python_rcl`.

The ctypes backend searches for `t32api64.so` in: `T32_API_LIB` env var → `api_lib_path` SDN config → `/opt/t32/bin/pc_linux64/t32api64.so` → `/opt/t32/bin/t32api64.so` → `t32api64.so` (CWD).

## Status Bar

Every `t32_cmd_run`, `t32_cmm_run`, `t32_eval`, and dialog tool response includes:

```json
{
  "gui_status": {
    "message_line": "system halted",
    "message_type": "info",
    "debug": "system ready, stopped",
    "mode": "HLL",
    "system": "Up",
    "task": "idle",
    "cores": "0",
    "target_state": "stopped"
  },
  "status_bar": {"message": "system halted", "type": "info"},
  "target_state": "stopped"
}
```

- `gui_status`: structured TRACE32 bottom/status-line snapshot
- `status_bar.message`: Current TRACE32 status bar text
- `status_bar.type`: `info`, `warning`, or `error`
- `target_state`: `running`, `stopped`, or `unknown`

The `gui_status` object is always present on T32 MCP tool responses, including tool errors. Fields that TRACE32 does not expose through the active backend are returned as empty strings, while normalized `target_state` always falls back to `unknown`.

With the ctypes backend, status is queried via `T32_GetMessage()` and `STATE.RUN()` directly. With subprocess backends, two additional EVAL commands are sent.

## Error Checking

### Automatic Error Append

When a command produces subprocess stderr, an `errors` array is appended. When TRACE32 is still carrying an older warning or error in its message buffer, it is surfaced as `last_buffered_error` so callers can distinguish stale state from the current command result:

```json
{
  "command": "Data.Set 0x0 0xFF",
  "output": "",
  "status_bar": {"message": "access denied", "type": "error"},
  "target_state": "stopped",
  "last_buffered_error": [
    {"source": "t32_message", "type": "error", "message": "access denied"},
  ],
  "errors": [
    {"source": "stderr", "type": "error", "message": "t32rem: command failed"}
  ]
}
```

The `errors` and `last_buffered_error` keys are omitted when empty. Sources:
- `t32_message`: TRACE32 message area (warning or error type)
- `stderr`: subprocess stderr output (t32rem or python bridge)

## Dialog Tools

`t32_dialog_parse` now returns normalized dialog metadata for every parsed widget type, including unlabeled `EDIT`, `CHECKBOX`, `CHOOSEBOX`, `PULLDOWN`, `BUTTON`, and `DEFBUTTON` items.

Per element, the response includes:
- `label`: explicit label when present, otherwise an auto-generated virtual label
- `declared_label`: raw CMM label, empty when the label was generated
- `generated_label`: `true` when the label was synthesized for LLM/UI use
- `clickable`, `queryable`, `settable`
- `query_type`: `boolean`, `string`, `value`, or empty
- `supported_actions`
- `runtime_access`: `label`, `callback`, or `parse_only`

Generated labels are stable within a parse result and make unlabeled widgets visible to the caller. Runtime behavior depends on `runtime_access`:
- `label`: safe to use with `t32_dialog_get`, `t32_dialog_set`, and `t32_dialog_click`
- `callback`: clickable through `t32_dialog_click`, which runs the parsed callback directly
- `parse_only`: visible to analysis/LLM tooling, but TRACE32 cannot address it without an explicit label

`t32_dialog_set` and `t32_dialog_click` accept `mode: "sync" | "async"`:
- `sync` is the default and polls `PRACTICE.STATE()` until idle or timeout
- `async` dispatches immediately and returns a completion hint telling the caller to poll `EVAL PRACTICE.STATE()` until it returns `0`

`t32_dialog_set` supports `set`, `select`, `deselect`, `disable`, and `enable`. The handler validates the parsed widget type first when dialog metadata is available, so boolean-only actions do not run against text or header widgets.

### `t32_error_check` Tool

Explicitly query TRACE32 error state without running a command:

```text
t32_error_check()
```

Returns:
- `message`: Current message area text
- `type`: `info`, `warning`, or `error`
- `stderr`: Last subprocess stderr (empty for ctypes backend)
- `practice_state`: PRACTICE script state (0=idle, 1=running, 2=dialog, -1=unknown)
- `has_error`: `true` if any error/warning detected

## Blocking Guard

Both `t32_cmd_run` and `t32_cmm_run` use `t32_check_blocking()` before execution in headless mode.

Classification:
- `BLOCK`: execution is refused unless `force: "true"` is provided
- `WARN`: execution continues, but the result includes caution metadata
- `INFO`: execution continues with a note about no-op or display-only behavior

Typical blocking commands:
- `DIALOG.OK`
- `DIALOG.YESNO`
- `DIALOG.FILE`
- `DIALOG.DIR`
- `DIALOG.STRING`
- `INKEY`
- `ENTER`
- `PAUSE`
- `STOP`
- `SCREEN.WAIT`

Typical warning/info commands:
- `WAIT`
- `MENU.ReProgram`
- `SCREEN.ON`
- `WINPOS`

Example blocked call:

```text
t32_cmd_run(command: "ENTER")
```

Use `force: "true"` only when the caller knows the command is safe in its specific environment.

## Window Catalog

The MCP window tools are catalog-driven. `config/t32/catalogs/windows.sdn` defines the visible window keys, open commands, capture commands, and optional metadata.

Supported optional fields:
- `capture_mode`
- `arch`
- `notes`

The MCP surfaces that metadata through:
- `t32_window_list`
- `t32_window_describe`
- `t32:///windows`

Useful built-in keys include:
- `register_view`
- `trace_list`
- `riscv_csr_view`
- `flash_status`
- `system_status`
- `nexus_trace`

The current RISC-V/status windows use these commands:
- `riscv_csr_view`: `Register.view /SpotLight /CSR`
- `flash_status`: `FLASH.List`
- `system_status`: `System.state`
- `nexus_trace`: `Trace.List /Nexus`

The bundled TRACE32 command database used by `t32_cmm_commands` is helpful, but it is not the source of truth for the window catalog. Catalog entries may legitimately use commands that are not present in the embedded command list.

## Recommended Workflow

1. `t32_session_open(host: "localhost", port: "20000")`
2. `t32_cmd_run(command: "SYStem.Up")`
3. `t32_window_capture(window: "system_status")`
4. `t32_window_capture(window: "riscv_csr_view")`
5. `t32_cmd_run(command: "Break.Set main")`
6. `t32_window_capture(window: "nexus_trace")`

## Related Docs

- `examples/10_tooling/trace32_tools/README.md`
- `doc/07_guide/tools/t32_cli.md`
