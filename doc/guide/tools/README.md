# TRACE32 Tools — Overview

Suite of TRACE32 debugging tools written in Simple, providing CLI, MCP, LSP, and DAP interfaces for Lauterbach probe automation.

---

## Components

| Tool | Description | Entry Point |
|------|-------------|-------------|
| **T32 CLI** | Command-line interface for TRACE32 sessions | `src/app/t32_cli/mod.spl` |
| **MCP T32 LSP/DAP** | MCP server: 26 tools for session, window, CMM LSP, DAP | `src/app/mcp_t32/main.spl` |
| **MCP CMM CLI** | MCP server: 8 tools for GUI-to-CLI conversion | `examples/10_tooling/trace32_tools/cmm_lsp/mod.spl` |
| **CMM LSP** | Language server for PRACTICE/CMM scripts | `examples/10_tooling/trace32_tools/cmm_lsp/lsp_server.spl` |
| **DAP Adapters** | Debug Adapter Protocol for TRACE32 and GDB bridge | `src/lib/nogc_sync_mut/dap/adapter/` |

---

## Quick Start

### CLI

```bash
simple t32 sessions open localhost 20000 stm32wb ARM
simple t32 windows
simple t32 window show register_view
simple t32 shell   # interactive REPL
```

### MCP Servers

Add to `.mcp.json`:

```json
{
  "mcpServers": {
    "simple-mcp-t32-lsp-dap": {
      "command": "bin/simple",
      "args": ["src/app/mcp_t32/main.spl"]
    }
  }
}
```

Test: `echo '{"jsonrpc":"2.0","id":"1","method":"tools/list"}' | bin/simple src/app/mcp_t32/main.spl`

---

## Architecture

```
Simple Code  →  t32rem / RCL API (UDP)  →  PowerView  →  JTAG Probe  →  Target MCU
                                               ↓
                                      GDB Back-End (TCP)  →  GDB Client
```

Two remote interfaces:

| Interface | Protocol | Default Port | Use Case |
|-----------|----------|-------------|----------|
| `t32_native` (RCL) | UDP NETASSIST | 20000 | Control PowerView directly |
| `t32_gdb` (RSP) | TCP | 30000 | GDB debugging through TRACE32 |

---

## Tool Inventory

### MCP T32 LSP/DAP — 26 Tools

**Session (9):** `t32_sessions_list`, `t32_session_open`, `t32_session_resume`, `t32_session_close`, `t32_core_list`, `t32_core_select`, `t32_cmd_run`, `t32_cmm_run`, `t32_eval`

**Window (5):** `t32_window_list`, `t32_window_open`, `t32_window_capture`, `t32_window_describe`, `t32_screenshot`

**Action/Field (6):** `t32_action_invoke`, `t32_field_get`, `t32_field_set`, `t32_history_tail`, `t32_resources_list`, `t32_resource_read`

**CMM LSP (6):** `cmm_parse`, `cmm_lint`, `cmm_hover`, `cmm_complete`, `cmm_goto_def`, `cmm_symbols`

### MCP CMM CLI — 8 Tools

**Converter (3):** `cmm_convert_file`, `cmm_convert_dir`, `cmm_preview`

**Validator (3):** `cmm_bulk_validate`, `cmm_check_gui`, `cmm_report`

**Runner (2):** `cmm_run_converted`, `cmm_diff_original`

---

## SDN Catalogs

Window definitions, actions, and fields loaded from `config/t32/catalogs/`:

| File | Content |
|------|---------|
| `windows.sdn` | Window definitions (key, title, kind, open/capture commands) |
| `actions.sdn` | Action definitions (key, label, type, command template) |
| `fields.sdn` | Field definitions (key, label, value type, scope) |

---

## Host Prerequisites

- Lauterbach TRACE32 installed at `/opt/t32`
- USB probe connected and visible (`lsusb | grep 0897`)
- udev rule installed for `/dev/lauterbach/trace32/` device path
- Run `scripts/t32_host_setup.shs` for one-shot host configuration

---

## Source Locations

All T32 tools live in the [`trace32_tools`](https://github.com/ormastes/trace32_tools) submodule at `examples/10_tooling/trace32_tools/`. Symlinks at the original paths preserve import compatibility.

| Component | Submodule Path | Symlink |
|-----------|---------------|---------|
| T32 CLI | `trace32_tools/t32_cli/` (9 files) | `src/app/t32_cli/` |
| MCP T32 server | `trace32_tools/t32_mcp/` (6 files) | `src/app/mcp_t32/` |
| T32 LSP MCP server | `trace32_tools/t32_lsp_mcp/` (4 files) | — |
| CMM LSP/parser | `trace32_tools/cmm_lsp/` (43 files) | `examples/10_tooling/cmm_lsp/` |
| Config/catalogs | `trace32_tools/config/` (5 files) | — |
| Test fixtures | `trace32_tools/test_fixtures/` (47 CMM scripts) | — |
| DAP adapters | `src/lib/nogc_sync_mut/dap/adapter/` | — |
| RCL protocol | `src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl` | — |
| GDB bridge | `src/lib/nogc_sync_mut/debug/remote/protocol/t32_gdb_bridge.spl` | — |
| Shell helpers | `scripts/t32_*.shs` | — |

---

## Detailed Guides

- [T32 CLI](t32_cli.md) — CLI commands, interactive shell, SDN catalogs
- [MCP T32 Servers](mcp_t32.md) — MCP setup, tool reference, example workflows
- [Linux Setup](../backend/trace32_linux_setup.md) — udev rules, probe access, PowerView startup
- [Docker Experiment](../backend/trace32_docker_experiment.md) — containerized T32 testing
- [Remote Interfaces Research](../../research/trace32_remote_interfaces_2026-03-08.md) — RCL vs GDB protocol analysis
