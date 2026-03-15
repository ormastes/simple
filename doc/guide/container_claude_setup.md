# Claude Code + Simple MCP/LSP — Fresh Linux Container Setup

Quick guide to install Claude Code with Simple language MCP/LSP and TRACE32 MCP/LSP
on a fresh Linux container (Ubuntu/Debian).

---

## 1. Prerequisites

```bash
# Node.js 18+ (for Claude Code)
curl -fsSL https://deb.nodesource.com/setup_22.x | bash -
apt-get install -y nodejs git bash

# Claude Code — official CLI
npm install -g @anthropic-ai/claude-code
```

> **Docs:** https://docs.anthropic.com/en/docs/claude-code/overview

---

## 2. Clone & Build Simple

```bash
git clone https://github.com/<org>/simple.git
cd simple

# Build the release binary (required for MCP/LSP servers)
bin/simple build --release
```

This produces `bin/release/simple` — the runtime all servers need.

---

## 3. Install MCP Servers (Simple + T32)

```bash
# Auto-installs .mcp.json to project root (platform-aware)
sh config/mcp/install.shs
```

This copies the correct `.mcp.json` for your OS. The file configures two MCP servers:

| Server | Command | What it does |
|--------|---------|--------------|
| `simple-mcp` | `bin/simple_mcp_server` | 69 tools: diagnostics, debugging, VCS, testing, code analysis |
| `t32-mcp` | `bin/t32_mcp_server` | TRACE32 debugger integration (requires T32 hardware/sim) |

**Paths (relative to project root):**
- MCP config: `.mcp.json`
- Simple MCP binary: `bin/simple_mcp_server`
- T32 MCP binary: `bin/t32_mcp_server`
- Both are bash scripts that exec `bin/release/simple` with the appropriate `.spl` entry point

---

## 4. LSP Servers (Simple + CMM)

LSP servers provide code intelligence for `.spl`/`.shs` (Simple) and `.cmm` (TRACE32 PRACTICE) files.

### Simple LSP

```bash
bin/release/simple run src/app/lsp/main.spl
```

### CMM LSP (TRACE32 PRACTICE scripts)

```bash
bin/release/simple examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp
```

### Claude Code LSP Plugin Config

Place these in the project's plugin directories or configure manually:

**Simple LSP** (`.lsp.json`):
```json
{
  "languages": [
    {
      "fileExtensions": [".spl", ".shs"],
      "languageId": "simple",
      "command": ["bin/release/simple", "run", "src/app/lsp/main.spl"],
      "initializationOptions": {}
    }
  ]
}
```

**CMM LSP** (`.lsp.json`):
```json
{
  "languages": [
    {
      "fileExtensions": [".cmm"],
      "languageId": "cmm",
      "command": ["bin/release/simple", "examples/10_tooling/trace32_tools/cmm_lsp/mod.spl", "--lsp"],
      "initializationOptions": {}
    }
  ]
}
```

---

## 5. Verify

```bash
# Start Claude Code in the project directory
cd /path/to/simple
claude

# Inside Claude, MCP tools are auto-discovered from .mcp.json
# Try: ask Claude to use simple-mcp tools
```

---

## All Paths Summary

| Component | Path (from project root) |
|-----------|-------------------------|
| **MCP config** | `.mcp.json` |
| **Simple MCP server** | `bin/simple_mcp_server` |
| **T32 MCP server** | `bin/t32_mcp_server` |
| **Simple runtime** | `bin/release/simple` |
| **Simple LSP entry** | `src/app/lsp/main.spl` |
| **CMM LSP entry** | `examples/10_tooling/trace32_tools/cmm_lsp/mod.spl` |
| **MCP install script** | `config/mcp/install.shs` |
| **Marketplace plugins** | `tools/claude-plugin/marketplace/plugins/` |

---

## T32 MCP Notes

The T32 MCP server requires a running TRACE32 instance (hardware probe or simulator).
See `config/t32/` for headless container setup with Docker Compose.
Without T32 hardware, the `t32-mcp` entry in `.mcp.json` can be removed.
