# T32 MCP Guide

The TRACE32 MCP server lives in `examples/10_tooling/trace32_tools/t32_mcp/` and exposes 23 tools for live TRACE32 session control. The paired CMM analysis server lives in `examples/10_tooling/trace32_tools/t32_lsp_mcp/`.

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
```

Override order:
1. CLI flags such as `--host=` and `--port=`
2. environment variables such as `T32_DEFAULT_HOST`, `T32_DEFAULT_PORT`, `T32_RCL_HOST`, `T32_RCL_PORT`, `T32_BACKEND_PREFERENCE`
3. `config/t32/t32_mcp.sdn`

`backend_preference: python_rcl` prefers the Python RCL bridge when available. Otherwise the server uses `t32rem` first and falls back to the Python bridge.

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
- `doc/guide/tools/t32_cli.md`
