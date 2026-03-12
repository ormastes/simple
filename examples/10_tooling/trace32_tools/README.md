# TRACE32 MCP Tools

MCP servers and development tools for [Lauterbach TRACE32](https://www.lauterbach.com/en/) hardware debuggers. Enables AI assistants (Claude, Copilot, etc.) to control debug sessions, analyze CMM scripts, and interact with embedded targets.

**Protocol:** [MCP 2025-06-18](https://modelcontextprotocol.io/) (JSON-RPC 2.0, stdio transport)

## Install

### Pre-built binaries (recommended)

```bash
# One-line install (Linux x86_64)
curl -fsSL https://raw.githubusercontent.com/ormastes/simple/main/examples/10_tooling/trace32_tools/install.sh | bash
```

Or download from [GitHub Releases](https://github.com/ormastes/simple/releases?q=t32-v):

| Binary | Platform | Description |
|--------|----------|-------------|
| `t32-mcp-server` | Linux, Windows | TRACE32 debug session control — 20 MCP tools |
| `t32-lsp-mcp-server` | Linux, Windows | CMM language intelligence — 6 MCP tools |
| `cmm-lsp` | Linux, Windows | CMM Language Server (LSP over stdio) |
| `t32-cli` | Linux, Windows | Interactive TRACE32 CLI shell |

### Manual download

```bash
# Download specific binary
VERSION="1.0.0"
curl -fsSL -o t32-mcp-server \
  "https://github.com/ormastes/simple/releases/download/t32-v${VERSION}/t32-mcp-server-linux-x86_64"
chmod +x t32-mcp-server
```

### Build from source

Requires the [Simple](https://github.com/ormastes/simple) compiler:

```bash
git clone https://github.com/ormastes/simple.git
cd simple
# Build the compiler first (see main README)
bin/release/simple native-build \
  --source src --entry examples/10_tooling/trace32_tools/t32_mcp/main.spl \
  -o t32-mcp-server
```

---

## Setup

### Claude Code

Add to `.mcp.json` in your project root:

```json
{
  "mcpServers": {
    "t32-mcp": {
      "command": "t32-mcp-server"
    },
    "t32-lsp-mcp": {
      "command": "t32-lsp-mcp-server"
    }
  }
}
```

> If the binary is not in PATH, use the full path: `"/home/user/.local/bin/t32-mcp-server"`

### Claude Desktop

Add to `~/.config/Claude/claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "t32-mcp": {
      "command": "/path/to/t32-mcp-server"
    },
    "t32-lsp-mcp": {
      "command": "/path/to/t32-lsp-mcp-server"
    }
  }
}
```

### Verify

```bash
# Check the server responds to MCP initialize
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}' | t32-mcp-server

# List available tools
echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | t32-mcp-server
```

---

## Tools

### T32 MCP Server (20 tools)

Controls live TRACE32 debug sessions. Requires a running TRACE32 PowerView instance.

| Category | Tools | Description |
|----------|-------|-------------|
| **Session** | `t32_sessions_list`, `t32_session_open`, `t32_session_resume`, `t32_session_close` | Connect to TRACE32 PowerView instances |
| **Core** | `t32_core_list`, `t32_core_select` | Multi-core target management |
| **Command** | `t32_cmd_run`, `t32_cmm_run`, `t32_eval` | Execute PRACTICE commands and scripts |
| **Window** | `t32_window_list`, `t32_window_open`, `t32_window_capture`, `t32_window_describe`, `t32_screenshot` | Capture register views, memory dumps, source listings |
| **Action** | `t32_action_invoke`, `t32_field_get`, `t32_field_set` | Named actions from SDN catalogs |
| **History** | `t32_history_tail`, `t32_resources_list`, `t32_resource_read` | Command history and MCP resources |

**Example workflow:**

```
1. t32_session_open(host: "localhost", port: "20000")
2. t32_cmd_run(command: "SYStem.Up")
3. t32_window_capture(window: "register_view")
4. t32_cmd_run(command: "Break.Set main")
5. t32_cmd_run(command: "Go")
6. t32_window_capture(window: "var_local")
```

### T32 LSP MCP Server (6 tools)

CMM (PRACTICE) script analysis. Standalone — no TRACE32 hardware needed.

| Tool | Description |
|------|-------------|
| `cmm_parse` | Parse CMM script, return AST summary |
| `cmm_diagnostics` | Errors, warnings, unused macros, unreachable code |
| `cmm_complete` | Auto-complete commands and PRACTICE functions |
| `cmm_hover` | Command/function documentation |
| `cmm_symbols` | Document symbols (labels, macros) |
| `cmm_validate_cli` | Validate CLI-mode converted scripts |

### CMM Language Server (LSP)

Full LSP implementation for `.cmm` files, for IDE integration:

- **Completions** — 100+ TRACE32 commands, 50+ PRACTICE functions, macro names
- **Hover** — Command documentation with syntax descriptions
- **Go to definition** — Jump to label and macro definitions
- **Document symbols** — Labels and macros as outline
- **Diagnostics** — Parse errors, undefined labels, unreachable code, unused macros

See [`cmm_lsp/README.md`](cmm_lsp/README.md) for IDE-specific setup.

### T32 Interactive CLI

Interactive shell for TRACE32 session management with SDN catalog support.

---

## Requirements

| Tool | TRACE32 Required | Notes |
|------|:---:|-------|
| t32-mcp-server | Yes | Needs running PowerView instance with Remote API enabled |
| t32-lsp-mcp-server | No | Pure CMM analysis, no hardware needed |
| cmm-lsp | No | Pure CMM analysis |
| t32-cli | Yes | Interactive session management |

**TRACE32 setup:** Enable the Remote API in PowerView: `RCL.Port 20000` or set `RCL=NETASSIST` in your `config.t32`.

---

## Directory Structure

```
trace32_tools/
├── cmm_lsp/           # CMM Language Server (LSP over stdio)
├── t32_mcp/           # TRACE32 Control MCP Server
├── t32_lsp_mcp/       # CMM Intelligence MCP Server
├── t32_cli/           # Interactive T32 CLI Shell
├── config/            # T32 configuration & catalogs
│   └── catalogs/      # Action, field, window definitions (SDN)
├── test_fixtures/     # CMM script test corpus (29 scripts)
│   ├── riscv/         # RISC-V platform scripts
│   ├── stm32/         # STM32 platform scripts (real hardware)
│   ├── web/           # Various SoC platform scripts
│   └── expected_cli/  # CLI-mode conversions (batch-friendly)
├── install.sh         # One-line installer
└── README.md          # This file
```

## Test Fixtures

29 CMM scripts across three platform families:

- **RISC-V** (8 scripts) — BL602, CH32V307, ESP32-C3, SiFive E31
- **STM32** (6 scripts) — Real hardware scripts for STM32H7 and STM32WB
- **Web/SoC** (15 scripts) — EDK2/UEFI, i.MX6, PolarFire, R-Car3, QNX

Plus 18 CLI batch-mode conversions under `test_fixtures/expected_cli/`.

---

## CI/CD

Binaries are built automatically on every push to `main` that touches `trace32_tools/`:

- **Build workflow:** [`.github/workflows/t32-tools-build.yml`](../../.github/workflows/t32-tools-build.yml) — builds + smoke tests
- **Release workflow:** [`.github/workflows/t32-tools-release.yml`](../../.github/workflows/t32-tools-release.yml) — publishes to GitHub Releases on `t32-v*` tags

Platforms: Linux x86_64 (primary), Windows MinGW x86_64 (cross-compiled).

---

## License

Part of the [Simple](https://github.com/ormastes/simple) project.
