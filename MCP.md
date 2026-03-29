# Simple Language — MCP Servers, Plugins & Extensions

All MCP servers, AI CLI plugins, and dev skill integrations produced by this project.

## Marketplace Front Pages

| Platform | Marketplace URL | Our Listing |
|----------|----------------|-------------|
| **Claude Code** | [anthropics/claude-plugins-official](https://github.com/anthropics/claude-plugins-official) / [claudemarketplaces.com](https://claudemarketplaces.com/) | Not submitted |
| **Gemini CLI** | [geminicli.com/extensions](https://geminicli.com/extensions/) | Not discoverable (need GitHub topic) |
| **Codex** | [developers.openai.com/codex/plugins](https://developers.openai.com/codex/plugins) / [openai/skills](https://github.com/openai/skills) | Not submitted (plugin system launched 2026-03-26) |
| **MCP Registry** | [registry.modelcontextprotocol.io](https://registry.modelcontextprotocol.io/) | Not registered |

## Deployment Status

| Market | Status | Blocking Step |
|--------|--------|---------------|
| **npm** (`@simple-lang/mcp-server`) | Not published | `npm org create simple-lang` + `npm publish --access public` |
| **MCP Registry** | Not registered | npm publish first, then `npx @anthropic-ai/mcp-publisher register` |
| **Gemini CLI Gallery** | Not discoverable | Need public GitHub repo + `gemini-cli-extension` topic |
| **Claude Marketplace** | Local only | Package exists; submit to [anthropics/claude-plugins-official](https://github.com/anthropics/claude-plugins-official) or community marketplaces |
| **Codex Plugins** | Ad-hoc only | Convert `.codex/skills/` to plugin bundle; submit to [openai/skills](https://github.com/openai/skills) catalog |
| **GitHub Releases** | None | `gh release create` with platform binaries needed for npm postinstall |

All infrastructure, manifests, and packaging scripts are ready. No external publishing has been done yet.

---

## MCP Servers

Four MCP servers, all native binaries (no Node.js runtime needed). Each wraps `bin/release/simple` via thin shell/cmd launchers.

| MCP Server | Launcher | Source | Description |
|------------|----------|--------|-------------|
| **simple-mcp** | `bin/simple_mcp_server` | `src/app/mcp/main.spl` | 68 tools — code intelligence, debugging (DAP), build, test, VCS (jj), search, analysis |
| **simple-lsp-mcp** | `bin/simple_lsp_mcp_server` | `src/app/simple_lsp_mcp/main.spl` | LSP bridge — diagnostics, completions, hover, go-to-definition for `.spl`/`.shs` files |
| **t32-mcp** | `bin/t32_mcp_server` | `examples/10_tooling/trace32_tools/t32_mcp/main.spl` | TRACE32 probe control — RCL commands, memory read/write, register access, SWD/JTAG |
| **t32-lsp-mcp** | `bin/t32_lsp_mcp_server` | `examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl` | CMM/PRACTICE LSP bridge — diagnostics, completions, hover for `.cmm` scripts |

Windows variants use `.cmd` launchers (`bin/simple_mcp_server.cmd`, etc.).

### Install MCP Servers (local project)

```bash
# Auto-detects platform (Linux/macOS/Windows) and copies correct .mcp.json
sh config/mcp/install.shs

# Windows CMD (no sh): manually copy
copy config\mcp\win\.mcp.json .mcp.json
```

Config files: `config/mcp/common/.mcp.json` (Linux/macOS), `config/mcp/win/.mcp.json` (Windows).

### Install via npm (global, for any project)

```bash
npm install -g @simple-lang/mcp-server
```

Then in any `.mcp.json`:
```json
{ "mcpServers": { "simple-mcp": { "command": "npx", "args": ["@simple-lang/mcp-server"] } } }
```

npm package: `tools/mcp-registry/package.json` (`@simple-lang/mcp-server`). Downloads platform binary on `postinstall`.

---

## Claude Code Plugins

Three plugins distributed via local marketplace or standalone install.

| Plugin | Type | Description | Config |
|--------|------|-------------|--------|
| **simple-mcp** | MCP | Simple MCP server integration | `tools/claude-plugin/simple-mcp/` |
| **simple-lsp** | LSP | Language server for `.spl`/`.shs` (diagnostics, completions, hover) | `tools/claude-plugin/simple-lsp/` |
| **cmm-lsp** | LSP | TRACE32 CMM/PRACTICE language server for `.cmm` | `tools/claude-plugin/marketplace/plugins/cmm-lsp/` |

### Install via Local Marketplace

```bash
# Register local marketplace
claude plugin marketplace add tools/claude-plugin/marketplace

# Install plugins
claude plugin install simple-mcp@simple-local
claude plugin install simple-lsp@simple-local
claude plugin install cmm-lsp@simple-local
```

Marketplace definition: `tools/claude-plugin/marketplace/.claude-plugin/marketplace.json`

### Install via Direct MCP Registration

```bash
claude mcp add simple-mcp -- bin/simple_mcp_server
claude mcp add simple-lsp-mcp -- bin/simple_lsp_mcp_server
claude mcp add t32-mcp -- bin/t32_mcp_server
claude mcp add t32-lsp-mcp -- bin/t32_lsp_mcp_server
```

### Package for Distribution

```bash
sh tools/claude-plugin/package_release_plugins.shs --version 0.9.2
# Output: build/release/plugins/
#   simple-mcp-claude-plugin-0.9.2.tar.gz
#   simple-lsp-claude-plugin-0.9.2.tar.gz
#   cmm-lsp-claude-plugin-0.9.2.tar.gz
```

Script: `tools/claude-plugin/package_release_plugins.shs`

---

## Claude Code Dev Skills & Agents

Skills (`.claude/skills/`) and agents (`.claude/agents/`) are auto-discovered by Claude Code when working in this project.

### Skills (7)

| Skill | File | Purpose |
|-------|------|---------|
| `/research` | `.claude/skills/research.md` | Local + domain research with agent teams |
| `/design` | `.claude/skills/design.md` | Architecture, UI, system tests, detail design |
| `/impl` | `.claude/skills/impl.md` | 15-phase implementation workflow |
| `/verify` | `.claude/skills/verify.md` | Production readiness codex |
| `/release` | `.claude/skills/release.md` | Release process and versioning |
| `/sync` | `.claude/skills/sync.md` | Pull/rebase/push with safety checks |
| `/refactor` | `.claude/skills/refactor.md` | Code quality refactoring workflow |

### Agents (12)

| Agent | File | Specialization |
|-------|------|----------------|
| code | `.claude/agents/code.md` | Writing/editing Simple code |
| test | `.claude/agents/test.md` | Tests, fixing failures |
| debug | `.claude/agents/debug.md` | Bug investigation, tracing |
| debug-analyst | `.claude/agents/debug-analyst.md` | DAP+LSP debug sessions |
| explore | `.claude/agents/explore.md` | Codebase search, research |
| docs | `.claude/agents/docs.md` | Documentation writing |
| vcs | `.claude/agents/vcs.md` | VCS operations (jj/git) |
| infra | `.claude/agents/infra.md` | MCP, database, stdlib, SFFI |
| build | `.claude/agents/build.md` | Building, releases |
| ml | `.claude/agents/ml.md` | Machine learning features |
| t32 | `.claude/agents/t32.md` | TRACE32 setup, probes |
| ui-design | `.claude/agents/ui-design.md` | UI design |

---

## Gemini CLI Extension

Auto-discovered via `gemini-cli-extension` GitHub topic. Manifest: `gemini-extension.json`

### What Gets Distributed

| Component | Count | Source |
|-----------|-------|--------|
| Commands | 12 | `.gemini/commands/*.toml` |
| MCP servers | 2 | `simple-mcp`, `simple-lsp-mcp` (via manifest) |
| Instructions | 1 | `GEMINI.md` |

Commands: `coding`, `design`, `impl`, `refactor`, `release`, `research`, `sync`, `verify`, `ui_design`, `visual_test`, `browser_research`, `stitch`

MCP servers in Gemini settings (`.gemini/settings.json`): `simple-mcp`, `simple-lsp-mcp`, `t32-mcp`, `t32-lsp-mcp`, plus `context-mode`, `context7`, `chrome-mcp`, `stitch-mcp`.

### User Installation

```bash
gemini extensions install nicobailon/simple
# Or from a specific version:
gemini extensions install nicobailon/simple --ref=v0.9.2
```

### Registration

1. Add GitHub topic `gemini-cli-extension` to repo (one-time)
2. Gallery auto-crawls daily — no manual submission needed

---

## Codex CLI Plugin

Codex launched a plugin system on **2026-03-26**. Plugins bundle skills + MCP server config into installable units.

Currently using **ad-hoc skill sharing** via `.codex/skills/` directory. Can be converted to a proper plugin bundle.

Config: `.codex/config.toml` — reads `AGENTS.md` natively + `CLAUDE.md` as fallback.

### MCP Servers (in config.toml)

All 4 MCP servers registered: `simple-mcp`, `simple-lsp-mcp`, `t32-mcp`, `t32-lsp-mcp`

### Skills (11, ad-hoc format)

| Skill | File |
|-------|------|
| research | `.codex/skills/research/SKILL.md` |
| design | `.codex/skills/design/SKILL.md` |
| impl | `.codex/skills/impl/SKILL.md` |
| verify | `.codex/skills/verify/SKILL.md` |
| release | `.codex/skills/release/SKILL.md` |
| architecture | `.codex/skills/architecture/SKILL.md` |
| system_test | `.codex/skills/system_test/SKILL.md` |
| coding | `.codex/skills/coding/SKILL.md` |
| sync | `.codex/skills/sync/SKILL.md` |
| refactor | `.codex/skills/refactor/SKILL.md` |
| mdsoc-architecture-writing | `.codex/skills/mdsoc-architecture-writing/SKILL.md` |

### Migration to Codex Plugin Format

To convert ad-hoc skills to a proper plugin bundle for the [Codex Plugins catalog](https://developers.openai.com/codex/plugins):

1. Bundle `.codex/skills/` + `.codex/config.toml` MCP entries into a plugin manifest
2. Install via `/plugins` command in Codex CLI
3. Submit to [openai/skills](https://github.com/openai/skills) catalog for public listing

---

## Deploy Script

```bash
scripts/deploy-marketplaces.shs                  # Show status of all markets
scripts/deploy-marketplaces.shs --check          # Check prerequisites (npm, gh, binaries)
scripts/deploy-marketplaces.shs --dry-run all    # Preview what would happen
scripts/deploy-marketplaces.shs all              # Deploy to all markets
scripts/deploy-marketplaces.shs npm              # npm publish only
scripts/deploy-marketplaces.shs mcp-registry     # MCP Registry only
scripts/deploy-marketplaces.shs gemini           # Gemini CLI extension (add GitHub topic)
scripts/deploy-marketplaces.shs claude           # Claude plugin (package + instructions)
scripts/deploy-marketplaces.shs codex            # Codex plugin (instructions)
scripts/deploy-marketplaces.shs github-release   # Create GitHub Release with binaries
```

Recommended order: `github-release` → `npm` → `mcp-registry` → `gemini` → `claude` → `codex`

---

## Marketplace Deployment Guide

### Claude Code — Plugin Marketplace

Local marketplace already set up. To publish externally:

1. Package plugins: `sh tools/claude-plugin/package_release_plugins.shs --version <ver>`
2. **Official directory:** Submit PR to [anthropics/claude-plugins-official](https://github.com/anthropics/claude-plugins-official) with plugin metadata
3. **Community marketplaces:** [claudemarketplaces.com](https://claudemarketplaces.com/), [buildwithclaude.com](https://buildwithclaude.com/) — follow each site's submission process
4. **Git-hosted marketplace:** Push `tools/claude-plugin/marketplace/` to a public repo; users add via `claude plugin marketplace add <git-url>`
5. Skills in `.claude/skills/` have YAML frontmatter and are plugin-compatible

### Gemini CLI — Extension Gallery

1. Ensure repo is **public** on GitHub
2. Add topic `gemini-cli-extension` to repo settings
3. Validate `gemini-extension.json` at repo root
4. Gallery crawls tagged repos daily — appears automatically

### MCP Server — Official Registry

```bash
# 1. Build and upload platform binaries to GitHub Release
gh release create v<ver> \
  bin/release/x86_64-unknown-linux-gnu/simple_mcp_server \
  bin/release/aarch64-apple-darwin/simple_mcp_server \
  bin/release/x86_64-pc-windows-msvc/simple_mcp_server.exe

# 2. Publish npm wrapper
cd tools/mcp-registry && npm publish --access public

# 3. Register with MCP Registry
npx @anthropic-ai/mcp-publisher register --server-json tools/mcp-registry/server.json
```

Registry URL: `https://registry.modelcontextprotocol.io/servers/@simple-lang/mcp-server`

### Codex — Plugin Catalog (new, 2026-03-26)

Codex now supports installable plugin bundles. To publish:

1. Convert `.codex/skills/` + MCP config into a Codex plugin bundle
2. Submit to [openai/skills](https://github.com/openai/skills) catalog via PR
3. Users install via `/plugins` command in Codex CLI or app
4. See [Codex Plugins docs](https://developers.openai.com/codex/plugins) for bundle format

---

## Version Synchronization

When releasing, update ALL version fields:

| File | Field |
|------|-------|
| `gemini-extension.json` | `version` |
| `tools/mcp-registry/package.json` | `version` |
| `tools/claude-plugin/marketplace/.claude-plugin/marketplace.json` | plugin versions |
| `tools/claude-plugin/simple-mcp/.claude-plugin/plugin.json` | `version` |
| `tools/claude-plugin/simple-lsp/.claude-plugin/plugin.json` | `version` |
| `tools/claude-plugin/marketplace/plugins/cmm-lsp/.claude-plugin/plugin.json` | `version` |
| `simple.sdn` | project version |
| `VERSION` | version file |

---

## Platform Support

| Platform | Triple | Status |
|----------|--------|--------|
| Linux x86_64 | `x86_64-unknown-linux-gnu` | Primary |
| Linux ARM64 | `aarch64-unknown-linux-gnu` | Planned |
| macOS x86_64 | `x86_64-apple-darwin` | Planned |
| macOS ARM64 | `aarch64-apple-darwin` | Planned |
| Windows x86_64 | `x86_64-pc-windows-msvc` | Planned |
| FreeBSD x86_64 | `x86_64-unknown-freebsd` | Planned |

---

## Related Documentation

- [AI CLI Registration Guide](doc/07_guide/tooling/ai_cli_registration.md) — detailed deployment steps
- [LLM Cooperative Dev Phases](doc/07_guide/llm_cooperative_dev_phase.md) — multi-LLM pipeline
- [bin/FILE.md](bin/FILE.md) — binary wrapper details
