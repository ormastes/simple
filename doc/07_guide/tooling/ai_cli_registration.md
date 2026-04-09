# AI CLI Tool Registration Guide

How to package and register Simple Language skills/plugins/extensions on their respective registries.

---

## Overview

| Instance | Registry | Auto-Discovery | Manual Steps |
|----------|----------|----------------|-------------|
| **Claude Code** | Local marketplace (already done) | N/A | Plugin install via `claude plugin` |
| **Gemini CLI** | geminicli.com/extensions gallery | Yes (GitHub topic) | Add topic only |
| **MCP Server** | registry.modelcontextprotocol.io | No | npm publish + mcp-publisher |

Related: `doc/07_guide/tooling/ai_command_parity.md` documents the shared workflow names used across Claude, Codex, and Gemini.

---

## 1. Claude Code Plugin

### Already Done

The Claude plugin infrastructure exists at `tools/claude-plugin/`:

```
tools/claude-plugin/
  marketplace/            # Local marketplace definition
    .claude-plugin/
      marketplace.json    # Marketplace metadata
    plugins/
      simple-mcp/         # MCP plugin package
      cmm-lsp/            # CMM LSP plugin package
  simple-mcp/             # Standalone MCP plugin
  simple-lsp/             # LSP plugin
  simple-codex/           # Codex-compatible MCP config
  package_release_plugins.shs  # Packaging script
```

### Install Locally

```bash
# Add local marketplace
claude plugin marketplace add tools/claude-plugin/marketplace

# Install Simple MCP plugin
claude plugin install simple-mcp@simple-local
```

### Direct MCP Registration (no marketplace)

```bash
claude mcp add simple-mcp -- bin/simple_mcp_server
claude mcp add simple-lsp-mcp -- bin/simple_lsp_mcp_server
```

### Package for Distribution

```bash
sh tools/claude-plugin/package_release_plugins.shs --version 0.9.2
# Produces: build/release/plugins/simple-mcp-claude-plugin-0.9.2.tar.gz
```

### Community Marketplace (future)

Skills in `.claude/skills/` (16 skills) and agents in `.claude/agents/` (11 agents) are already in the correct format. To publish to a community marketplace (CCPM, SkillHub, etc.):

1. Ensure each skill has proper YAML frontmatter (`name`, `description`)
2. Follow the specific marketplace's submission process
3. Skills with `disable-model-invocation: true` are manual-only

---

## 2. Gemini CLI Extension

### Prerequisites

- GitHub repository must be **public**
- `gemini-extension.json` at repo root (already created)

### Registration Steps

**Step 1: Add GitHub topic (one-time)**

1. Go to repository on GitHub
2. Click the gear icon next to "About" section
3. Add topic: `gemini-cli-extension`
4. Save

**Step 2: Wait for auto-discovery**

The Gemini CLI gallery crawls tagged repositories daily. Your extension will appear at the gallery automatically if validation passes. No manual submission needed.

### User Installation

Once discovered, users install with:

```bash
gemini extensions install nicobailon/simple
```

Or from a specific branch/tag:

```bash
gemini extensions install nicobailon/simple --ref=v0.9.2
```

### What Gets Distributed

| Component | Source |
|-----------|--------|
| 10 commands | `.gemini/commands/*.toml` |
| MCP servers | `simple-mcp`, `simple-lsp-mcp` (via manifest) |
| Instructions | `GEMINI.md` |
| Manifest | `gemini-extension.json` |

### Updating

Push updates to the repo. Gemini CLI checks release tags and prompts users to upgrade.

For faster installs, create GitHub Releases with archived assets:

```bash
gh release create v0.9.2 --title "v0.9.2" --notes "Release notes"
```

---

## 3. MCP Server Registry

### Prerequisites

- npm account (create at npmjs.com)
- npm organization `@simple-lang` (create at npmjs.com/org/create)
- GitHub account for mcp-publisher auth
- Platform binaries built and uploaded to GitHub Releases

### Step-by-Step

#### Step A: Claim npm scope

```bash
# Create npm org (one-time)
npm org create simple-lang
# Or use unscoped name if org unavailable
```

#### Step B: Build and upload platform binaries

```bash
# Build release binaries
bin/simple build --release

# Create GitHub Release with MCP server binaries
gh release create v0.9.2 \
  --title "v0.9.2" \
  --notes "Release with MCP server binaries" \
  bin/release/<platform>/simple_mcp_server \
  bin/release/<platform>/simple_mcp_server.exe
```

**Important:** Binary assets must be named `simple_mcp_server-<triple>[.exe]` to match the download script. Rename during upload if needed:

```bash
gh release upload v0.9.2 \
  bin/release/<platform>/simple_mcp_server#simple_mcp_server-<platform>
```

#### Step C: Publish to npm

```bash
cd tools/mcp-registry
npm login
npm publish --access public
```

#### Step D: Register with MCP Registry

```bash
npx @anthropic-ai/mcp-publisher register \
  --server-json tools/mcp-registry/server.json
# Opens GitHub OAuth for authentication
```

#### Step E: Verify

Check your server appears at:
- `https://registry.modelcontextprotocol.io/servers/@simple-lang/mcp-server`

### User Installation (after registration)

Users can then install via:

```bash
# npm global install
npm install -g @simple-lang/mcp-server
npm install -g @simple-lang/lsp-mcp-server

# Or use npx in MCP config
# .mcp.json:
# { "mcpServers": { "simple-mcp": { "command": "npx", "args": ["@simple-lang/mcp-server"] } } }
```

LSP bridge example:

```json
{
  "mcpServers": {
    "simple-lsp-mcp": {
      "command": "npx",
      "args": ["@simple-lang/lsp-mcp-server"]
    }
  }
}
```

---

## 4. Version Synchronization

When releasing a new version, update all manifests:

| File | Field |
|------|-------|
| `gemini-extension.json` | `version` |
| `tools/mcp-registry/package.json` | `version` |
| `tools/claude-plugin/marketplace/.claude-plugin/marketplace.json` | plugin versions |
| `tools/claude-plugin/simple-mcp/.claude-plugin/plugin.json` | `version` |
| `simple.sdn` | project version |
| `VERSION` | version file |

Consider adding version sync to the `/release` skill to automate this.

---

## 5. Supported Platforms

| Platform | Triple | MCP Binary | Status |
|----------|--------|-----------|--------|
| Linux x86_64 | `x86_64-unknown-linux-gnu` | `simple_mcp_server` | Primary |
| Linux ARM64 | `aarch64-unknown-linux-gnu` | `simple_mcp_server` | Planned |
| macOS x86_64 | `x86_64-apple-darwin` | `simple_mcp_server` | Planned |
| macOS ARM64 | `aarch64-apple-darwin` | `simple_mcp_server` | Planned |
| Windows x86_64 | `x86_64-pc-windows-msvc` | `simple_mcp_server.exe` | Planned |
| FreeBSD x86_64 | `x86_64-unknown-freebsd` | `simple_mcp_server` | Planned |

---

## 6. Troubleshooting

### Gemini extension not appearing in gallery

- Verify `gemini-cli-extension` topic is set on GitHub repo
- Ensure repo is public
- Validate `gemini-extension.json`: `cat gemini-extension.json | python3 -m json.tool`
- Gallery crawl is daily — wait 24 hours

### npm publish fails

- Ensure `@simple-lang` org exists: `npm org ls simple-lang`
- Check login: `npm whoami`
- Verify package.json version isn't already published

### MCP publisher fails

- Ensure npm package is published first
- Check GitHub OAuth scope includes repo read
- Verify `server.json` has valid JSON: `cat tools/mcp-registry/server.json | python3 -m json.tool`

### Binary download fails during npm install

- Check GitHub Release has correct asset names: `simple_mcp_server-<triple>`
- Binary falls back to PATH lookup — install from source as alternative
- Verify URL: `https://github.com/nicobailon/simple/releases/download/v<VERSION>/simple_mcp_server-<triple>`

---

## Related

- [LLM Cooperative Dev Phases](../llm_cooperative_dev_phase.md) — multi-LLM pipeline
- [AI CLI Coexistence Research](../../01_research/general/ai_cli_coexistence_2026-03-28.md) — configuration analysis
- [Multi-LLM Skill Refactor](../../01_research/local/multi_llm_skill_refactor.md) — skill design
