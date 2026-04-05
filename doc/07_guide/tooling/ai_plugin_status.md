# AI Plugin & Server Status Guide

Status of all MCP servers, LSP plugins, agent plugins, and their cross-platform support.

## MCP Servers

| Server | Binary | Config Key | Status | Startup |
|--------|--------|-----------|--------|---------|
| simple-mcp | `bin/release/simple_mcp_server` | `simple-mcp` | Working | Shared lib + background cache |
| simple-lsp-mcp | `bin/release/simple_lsp_mcp_server` | `simple-lsp-mcp` | Working | Shared lib + background cache |
| t32-mcp | `bin/release/t32_mcp_server` | `t32-mcp` | Working | Shared lib + native probe + cold/full frontend |
| t32-lsp-mcp | `bin/release/t32_lsp_mcp_server` | `t32-lsp-mcp` | Working | Shared lib + native probe + daemon support |
| obsidian-lsp-mcp | `bin/obsidian_lsp_mcp_server` | `obsidian-lsp-mcp` | Working | Direct exec |

**Shared startup library:** `config/mcp/mcp_startup_lib.sh`
- Compile cache (background, >1KB size check)
- Debug logging (env: `<SERVER>_DEBUG_LOG=1`)
- Native binary health probe with caching
- Runtime fallback chain: `SIMPLE_BINARY` > `bin/simple` > `bin/release/simple` > Rust bootstrap

## LSP Plugins (Claude Code Marketplace)

| Plugin | Marketplace | Server | Status |
|--------|------------|--------|--------|
| simple-lsp | `simple-local` | `bin/release/simple_lsp_mcp_server` | Enabled |
| cmm-lsp | `simple-local` | `bin/release/t32_lsp_mcp_server` | Disabled (optional) |
| markdown-oxide-lsp | `simple-local` | System `markdown-oxide` | Enabled |

**Marketplace:** `tools/claude-plugin/marketplace/.claude-plugin/marketplace.json`

## Agent Plugins (Cooperative Pipeline)

| Plugin | LLM | Pipeline Step | Purpose | Status |
|--------|-----|--------------|---------|--------|
| codex-research | OpenAI Codex CLI | Step 2 | Forked agent research + requirement selection | New |
| verify-agent | Claude + MCP | Post-impl | Production readiness verification via MCP tools | New |
| gemini-ui-design | Google Gemini CLI | Step 3 | TUI/GUI mockup design generation | New |

**Plugin location:** `tools/claude-plugin/<plugin-name>/`
**Build:** `tools/claude-plugin/<plugin-name>/build.sh`

## Cooperative Pipeline

```
Step 1: /research (Claude)        → doc/01_research/
Step 2: codex-research (Codex)    → doc/02_requirements/
Step 3: gemini-ui-design (Gemini) → doc/05_design/*_tui.md, *_gui.md
Step 4: /arch (Claude/Codex)      → doc/04_architecture/
Step 5: /design (Claude)          → doc/05_design/
Step 6: /impl (Claude)            → src/**/
Step 7: verify-agent (Claude+MCP) → verification report
```

## Cross-Platform Support

| Component | Linux | macOS | Windows (Git Bash) | Windows (native) |
|-----------|-------|-------|-------------------|------------------|
| MCP servers | Shell wrappers | Shell wrappers | Shell via bash | .cmd wrappers needed |
| LSP plugins | Via MCP | Via MCP | Via MCP | Via MCP |
| Agent plugins | CLI tools | CLI tools | CLI tools | CLI tools |
| Setup | `scripts/setup.sh` | `scripts/setup.sh` | `scripts/setup.sh` (Git Bash) | `scripts\setup.cmd` |

## Configuration Files

| Tool | Config File | Format |
|------|------------|--------|
| Claude Code | `.mcp.json` or project settings | JSON `mcpServers` |
| Codex CLI | `.codex/config.toml` | TOML `[mcp_servers.<name>]` |
| Gemini CLI | `.gemini/settings.json` | JSON `mcpServers` |

**Setup script** generates all 3 config files per platform.

## Troubleshooting

- **MCP server won't start:** Check `.simple/logs/<server>_stderr.log`
- **Debug logging:** Set `<SERVER>_DEBUG_LOG=1` env var, logs at `/tmp/<server>_debug_*/`
- **Bad cache:** Delete `.simple/cache/<server>/main.smf` (auto-rebuilds in background)
- **Native binary unhealthy:** Delete `/tmp/<server>_native_health_*.state` to re-probe
