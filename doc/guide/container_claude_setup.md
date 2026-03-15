# Claude Code + Simple MCP/LSP + TRACE32 — Fresh Linux Container Setup

Quick guide to install Claude Code with Simple language MCP/LSP and TRACE32 MCP/LSP
on a fresh Linux container (Ubuntu/Debian).

---

## 1. Prerequisites

### TRACE32 (pre-installed at `/opt/t32`)

TRACE32 must be installed at `/opt/t32` before starting.
Download from Lauterbach: https://www.lauterbach.com/frames.html?home.html

### Node.js + Claude Code

```bash
# Node.js 18+ (for Claude Code)
curl -fsSL https://deb.nodesource.com/setup_22.x | bash -
apt-get install -y nodejs git bash

# Claude Code — official CLI
npm install -g @anthropic-ai/claude-code
```

> **Claude Code docs:** https://docs.anthropic.com/en/docs/claude-code/overview
> **Claude Code plugins:** https://docs.anthropic.com/en/docs/claude-code/plugins

---

## 2. Clone & Build Simple

```bash
git clone https://github.com/ormastes/simple.git
cd simple

# Build the release binary (required for MCP/LSP servers)
bin/simple build --release
```

This produces `bin/release/simple` — the runtime all servers need.

---

## 3. Simple MCP Server (auto-discovered)

```bash
# Auto-installs .mcp.json to project root (platform-aware)
sh config/mcp/install.shs
```

Claude Code auto-discovers MCP servers from `.mcp.json` — no extra steps.

| Server | Command | What it does |
|--------|---------|--------------|
| `simple-mcp` | `bin/simple_mcp_server` | 69 tools: diagnostics, debugging, VCS, testing, code analysis |

---

## 4. TRACE32 Tools (T32 MCP + CMM LSP)

The T32 tools have their own installer and detailed documentation.
See: [`examples/10_tooling/trace32_tools/README.md`](../../examples/10_tooling/trace32_tools/README.md)

### Quick Setup (from repo checkout)

```bash
cd /path/to/simple

# T32 MCP — live debug session control (20 tools)
claude mcp add t32-mcp -- \
  $(pwd)/bin/release/simple \
  $(pwd)/examples/10_tooling/trace32_tools/t32_mcp/main.spl

# T32 LSP MCP — CMM script analysis (6 tools, no hardware needed)
claude mcp add t32-lsp-mcp -- \
  $(pwd)/bin/release/simple \
  $(pwd)/examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl

# CMM LSP plugin — IDE features for .cmm files
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install cmm-lsp@simple-local
```

### Alternative: One-line binary install

```bash
curl -fsSL https://raw.githubusercontent.com/ormastes/simple/main/examples/10_tooling/trace32_tools/install.sh | bash
```

Downloads pre-built binaries from [GitHub Releases](https://github.com/ormastes/simple/releases?q=t32-v).
See the [T32 tools README](../../examples/10_tooling/trace32_tools/README.md) for full details.

---

## 5. Simple LSP Plugin

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-lsp@simple-local
```

Add to `~/.claude/settings.json` if not already present:

```json
{
  "env": {
    "ENABLE_LSP_TOOL": "1"
  }
}
```

Restart Claude Code after installing for LSP servers to initialize.

---

## 6. Verify

```bash
cd /path/to/simple
claude
```

Inside Claude Code:
- **MCP:** Auto-discovered from `.mcp.json`. Ask Claude to use `simple-mcp` or `t32-mcp` tools.
- **LSP:** Active on `.spl`, `.shs`, `.cmm` files after plugin install + restart.

---

## All Paths Summary

| Component | Path (from project root) |
|-----------|-------------------------|
| **TRACE32 install** | `/opt/t32` (prerequisite) |
| **MCP config** | `.mcp.json` |
| **Simple MCP server** | `bin/simple_mcp_server` |
| **T32 MCP server** | `bin/t32_mcp_server` |
| **Simple runtime** | `bin/release/simple` |
| **Simple LSP entry** | `src/app/lsp/main.spl` |
| **CMM LSP entry** | `examples/10_tooling/trace32_tools/cmm_lsp/mod.spl` |
| **T32 MCP entry** | `examples/10_tooling/trace32_tools/t32_mcp/main.spl` |
| **T32 LSP MCP entry** | `examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl` |
| **T32 tools installer** | `examples/10_tooling/trace32_tools/install.sh` |
| **T32 tools docs** | `examples/10_tooling/trace32_tools/README.md` |
| **MCP install script** | `config/mcp/install.shs` |
| **Marketplace plugins** | `tools/claude-plugin/marketplace/plugins/` |

---

## Publishing & Deployment

### What needs which account/key

| What to publish | Platform | Account needed | API key URL |
|-----------------|----------|----------------|-------------|
| **MCP server** | Official MCP Registry | GitHub account | https://registry.modelcontextprotocol.io/ |
| **MCP server** | Smithery | GitHub OAuth | https://smithery.ai/ |
| **Claude Code plugin** | Anthropic marketplace | Anthropic API key | https://console.anthropic.com/settings/keys |
| **VSCode extension** | VS Code Marketplace | Microsoft + Azure PAT | https://dev.azure.com/ (Personal Access Tokens) |
| **VSCode extension** | Open VSX | GitHub OAuth | https://open-vsx.org/user-settings/tokens |
| **Neovim plugin** | GitHub (lazy.nvim) | GitHub account | No key needed — just push to `ormastes/simple.nvim` |

### MCP — No Claude API key needed

MCP registry uses **GitHub OAuth** only. Publish flow:

```bash
npm publish                    # publish to npm first
npx mcp-publisher init         # generates server.json
npx mcp-publisher login        # GitHub OAuth
npx mcp-publisher publish      # push to registry.modelcontextprotocol.io
```

### Claude Code Plugin — Anthropic API key

Get key at: https://console.anthropic.com/settings/keys

### VSCode Extension (alpha/preview)

The extension is marked `"preview": true` in `package.json` (version `0.1.0-alpha.1`).

1. Create publisher at https://marketplace.visualstudio.com/manage
2. Generate Azure Personal Access Token at https://dev.azure.com/ → User Settings → Personal Access Tokens
3. Publish:

```bash
cd src/app/vscode_extension
npx vsce login simple-lang     # uses Azure PAT
npx vsce publish               # publishes as preview/alpha
```

For Open VSX (VSCodium, open-source editors):

1. Sign in at https://open-vsx.org/ with GitHub
2. Generate token at https://open-vsx.org/user-settings/tokens
3. Publish:

```bash
npx ovsx create-namespace simple-lang --pat <token>
npx ovsx publish --pat <token>
```

### Neovim Plugin (lazy.nvim)

No API key needed. Just push the plugin to GitHub:

```bash
# Create the simple.nvim repo from the nvim_plugin directory
# Users install with lazy.nvim:
```

```lua
-- lazy.nvim spec
{
  "ormastes/simple.nvim",
  ft = "simple",
  opts = {},
}
```

The plugin source lives at `src/app/nvim_plugin/`. To publish as a standalone repo,
mirror or subtree-push that directory to `github.com/ormastes/simple.nvim`.

---

## Links

| Resource | URL |
|----------|-----|
| Claude Code | https://docs.anthropic.com/en/docs/claude-code/overview |
| Claude Code Plugins | https://docs.anthropic.com/en/docs/claude-code/plugins |
| TRACE32 Download | https://www.lauterbach.com/frames.html?home.html |
| MCP Protocol | https://modelcontextprotocol.io/ |
| T32 Tools Releases | https://github.com/ormastes/simple/releases?q=t32-v |
| T32 Tools Installer | https://raw.githubusercontent.com/ormastes/simple/main/examples/10_tooling/trace32_tools/install.sh |

### API Key / Account URLs

| Platform | Sign up / Key URL |
|----------|-------------------|
| **Anthropic Console** (Claude API key) | https://console.anthropic.com/settings/keys |
| **Azure DevOps** (VSCode marketplace PAT) | https://dev.azure.com/ → User Settings → Personal Access Tokens |
| **VS Code Marketplace** (publisher) | https://marketplace.visualstudio.com/manage/createpublisher |
| **Open VSX** (token) | https://open-vsx.org/user-settings/tokens |
| **MCP Registry** (GitHub OAuth) | https://registry.modelcontextprotocol.io/ |
| **Smithery** (GitHub OAuth) | https://smithery.ai/ |
| **GitHub** (for nvim plugin) | https://github.com/settings/tokens |
