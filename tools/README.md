# Tools

Development and integration tools for the Simple Language project.

---

## Directory Contents

| Directory | Description |
|-----------|-------------|
| `claude-plugin/` | Claude Code plugin bundles, local marketplace, and MCP configuration |

### `claude-plugin/simple-codex/`

MCP configuration that enables the Simple language MCP server:

```json
{
  "simple-codex": {
    "command": "simple",
    "args": ["mcp"]
  }
}
```

### `claude-plugin/simple-lsp/`

Claude Code LSP plugin bundle for `.spl` / `.shs` files.

### `claude-plugin/simple-mcp/`

Claude Code MCP plugin bundle for the main `simple-mcp` server.

### `claude-plugin/marketplace/`

Checked-in local Claude marketplace exposing:
- `simple-mcp`
- `simple-lsp`
- `cmm-lsp`

---

## Built-in Tools (via `bin/simple`)

All development tools are built into the Simple compiler binary. No external tool installations needed.

### Build & Quality

| Command | Description |
|---------|-------------|
| `simple build` | Debug build |
| `simple build --release` | Release build |
| `simple build lint` | Linter |
| `simple build fmt` | Formatter |
| `simple build check` | All quality checks |
| `simple build --warn-docs` | Documentation coverage warnings |

### Testing

| Command | Description |
|---------|-------------|
| `simple test` | Run all tests |
| `simple test path/to/spec.spl` | Run single test file |
| `simple test --list` | List available tests |
| `simple test --only-slow` | Run slow tests only |

### Code Analysis

| Command | Description |
|---------|-------------|
| `simple stats` | Code statistics with doc coverage |
| `simple doc-coverage` | Documentation coverage report |
| `simple doc-coverage --missing` | Show undocumented items |
| `simple todo-scan` | Update TODO tracking |

### Bug Tracking

| Command | Description |
|---------|-------------|
| `simple bug-add --id=X` | Add bug entry |
| `simple bug-gen` | Generate bug report |

### Code Fixes

| Command | Description |
|---------|-------------|
| `simple fix file.spl --dry-run` | Preview automated fixes |

---

## MCP Servers

Simple ships multiple MCP servers for AI tool integration:

| Server | Command | Tools | Description |
|--------|---------|-------|-------------|
| **Simple MCP** | `simple mcp` | 68 | Main server: code query, project tools, build/test/debug, resources, prompts |
| **MCP T32 LSP/DAP** | `simple src/app/mcp_t32/main.spl` | 26 | TRACE32 session, window, CMM LSP, DAP |
| **MCP CMM CLI** | `simple examples/10_tooling/cmm_lsp/mod.spl` | 8 | CMM GUI-to-CLI conversion, validation |

See [MCP guide](../doc/guide/tooling/mcp.md) for setup details.

---

## TRACE32 Tools

Suite of Lauterbach TRACE32 debugging tools:

- **T32 CLI** — command-line session management (`simple t32 <cmd>`)
- **MCP T32** — AI-integrated debug session control (26 + 8 tools)
- **CMM LSP** — PRACTICE/CMM language server (completion, hover, goto-def)
- **DAP adapters** — Debug Adapter Protocol for TRACE32 and GDB bridge

See [T32 tools guide](../doc/guide/tools/README.md) for full documentation.

---

## Tool Specifications

Detailed specifications for all tools: [`doc/spec/tooling/`](../doc/spec/tooling/)

| Spec | Tool |
|------|------|
| `simple_repl.md` | Interactive REPL |
| `simple_test.md` | Test runner |
| `simple_doc.md` | Documentation generator |
| `simple_todo.md` | TODO tracker |
| `simple_stats.md` | Code statistics |
| `simple_new.md` | Project scaffolding |
| `simple_grep.md` | AST-aware grep |
| `simple_deps.md` | Dependency graph |
| `simple_dead.md` | Dead code detector |
| `formatter.md` | Code formatter |
| `formatting_lints.md` | Lint rules |
| `build_audit.md` | Build audit |
| `basic_mcp.md` | MCP protocol |
| `vscode_extension.md` | VS Code integration |

---

## Tool Guides

User guides for tools: [`doc/guide/tooling/`](../doc/guide/tooling/)

| Guide | Topic |
|-------|-------|
| `mcp.md` | MCP server setup |
| `lsp_dap.md` | LSP/DAP debugging |
| `repl.md` | REPL usage |
| `jupyter.md` | Jupyter kernel |
| `treesitter.md` | TreeSitter integration |
| `dashboard.md` | Dashboard UI |
| `duplicate_check.md` | Duplicate detection |

TRACE32-specific guides: [`doc/guide/tools/`](../doc/guide/tools/)

| Guide | Topic |
|-------|-------|
| `README.md` | T32 tools overview |
| `t32_cli.md` | T32 CLI commands |
| `mcp_t32.md` | T32 MCP servers |
