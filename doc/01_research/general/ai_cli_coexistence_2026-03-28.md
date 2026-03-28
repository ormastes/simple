# AI CLI Coexistence: Claude Code + Codex CLI + Gemini CLI

**Date:** 2026-03-28
**Status:** Research Complete
**Purpose:** Map configuration, MCP, skills, agents, and root instructions across all three AI coding CLIs for unified project setup.

---

## Executive Summary

All three tools follow the same pattern: **root instruction file + config directory + MCP + skills/commands + agents**. They can coexist with zero conflict because each uses distinct file names and directories. The main challenge is keeping shared content (project instructions, MCP servers) in sync without duplication.

---

## 1. Root Instruction Files

The "project brain" file that each tool reads at startup.

| Tool | File Name | Global | Project | Subdirectory (JIT) |
|------|-----------|--------|---------|---------------------|
| **Claude Code** | `CLAUDE.md` | `~/.claude/CLAUDE.md` | `./CLAUDE.md` or `./.claude/CLAUDE.md` | Yes, loaded when files accessed |
| **Codex CLI** | `AGENTS.md` | `~/.codex/AGENTS.md` | `./AGENTS.md` | Yes, walks git root → cwd |
| **Gemini CLI** | `GEMINI.md` | `~/.gemini/GEMINI.md` | `./GEMINI.md` | Yes, loaded when tools access dir |

### Cross-Reading Support

| Tool | Reads CLAUDE.md? | Reads AGENTS.md? | Reads GEMINI.md? | Configurable? |
|------|-------------------|-------------------|-------------------|---------------|
| **Claude Code** | Yes (native) | No | No | No fallback config |
| **Codex CLI** | **Yes** (via fallback) | Yes (native) | No | `project_doc_fallback_filenames = ["CLAUDE.md"]` in `config.toml` |
| **Gemini CLI** | **Yes** (via fileName) | **Yes** (via fileName) | Yes (native) | `context.fileName = ["GEMINI.md", "AGENTS.md", "CLAUDE.md"]` in `settings.json` |

**Current project status:** All three tools read `CLAUDE.md` as context — configured via settings files, not `@` imports.

### Override / Local Variants

| Tool | Override File | Local/Personal |
|------|--------------|----------------|
| **Claude Code** | N/A | `.claude/settings.local.json` for settings (no CLAUDE.local.md) |
| **Codex CLI** | `AGENTS.override.md` (highest priority) | `~/.codex/AGENTS.override.md` |
| **Gemini CLI** | N/A | `~/.gemini/GEMINI.md` |

### Import Syntax

All three support modular instructions via imports:

| Tool | Syntax | Example |
|------|--------|---------|
| **Claude Code** | `@path/to/file` | `@AGENTS.md` (max 5 hops) |
| **Codex CLI** | N/A (concatenation only) | Walks directories, no cross-file import |
| **Gemini CLI** | `@./path/to/file` | `@./components/instructions.md` |

---

## 2. Configuration Directories

Each tool has its own project-level and user-level config directory.

### Project-Level (committed to git)

```
your-project/
  CLAUDE.md                    # Claude Code instructions
  AGENTS.md                    # Codex CLI instructions
  GEMINI.md                    # Gemini CLI instructions
  .mcp.json                    # Claude Code MCP servers
  .claude/                     # Claude Code config
    settings.json
    settings.local.json        # gitignored
    commands/
    skills/
    agents/
    memory/
    rules/
  .codex/                      # Codex CLI config
    config.toml
    hooks.json
    skills/
  .gemini/                     # Gemini CLI config
    settings.json
    commands/
    agents/                    # experimental
    sandbox.Dockerfile
    .env
```

### User-Level (personal, not committed)

```
~/
  .claude/                     # Claude Code global
    CLAUDE.md
    settings.json
    keybindings.json
    commands/
    skills/
    agents/
    projects/                  # auto-memory per project
      <project-hash>/
        memory/MEMORY.md
  .codex/                      # Codex CLI global
    config.toml
    auth.json
    AGENTS.md
    AGENTS.override.md
    skills/
      .system/                 # built-in skills
    memories/
    sessions/
  .gemini/                     # Gemini CLI global
    settings.json
    GEMINI.md
    commands/
    agents/
    extensions/
    mcp-oauth-tokens.json
```

### System-Level (admin/IT managed)

| Tool | macOS | Linux | Windows |
|------|-------|-------|---------|
| **Claude Code** | `/Library/Application Support/ClaudeCode/` | `/etc/claude-code/` | `C:\Program Files\ClaudeCode\` |
| **Codex CLI** | N/A | `/etc/codex/` | N/A |
| **Gemini CLI** | `/Library/Application Support/GeminiCli/` | `/etc/gemini-cli/` | `C:\ProgramData\gemini-cli\` |

---

## 3. MCP Server Configuration

### Where Each Tool Reads MCP Config

| Tool | Location | Format | Key |
|------|----------|--------|-----|
| **Claude Code** | `.mcp.json` (project root) | JSON | `mcpServers` |
| **Claude Code** | `~/.claude.json` (user) | JSON | `mcpServers` |
| **Codex CLI** | `.codex/config.toml` or `~/.codex/config.toml` | TOML | `[mcp_servers.<name>]` |
| **Gemini CLI** | `.gemini/settings.json` or `~/.gemini/settings.json` | JSON | `mcpServers` |

### MCP Servers Configured per Tool (current project)

| MCP Server | Claude | Codex | Gemini | Purpose |
|------------|--------|-------|--------|---------|
| **context7** | Yes | Yes | Yes | External library docs lookup |
| **simple-mcp** | Yes | Yes | Yes | Codebase query (workspace-symbols, references, hover) |
| **simple-lsp-mcp** | Yes | Yes | Yes | Code navigation (definition, completions) |
| **chrome-mcp** | -- | -- | Yes | Browser control, visual testing |
| **stitch-mcp** | -- | -- | Yes | Multi-file code editing |
| **jj-git-mcp** | Yes | -- | -- | JJ/Git VCS operations |

### Non-MCP CLI Tools

| Tool | Claude | Codex (AGENTS.md) | Gemini (GEMINI.md) | Purpose |
|------|--------|--------------------|--------------------|---------|
| **Playwright CLI** | -- | Yes (`npx playwright`) | Yes (`npx playwright`) | Web scraping, browser automation, domain research |

### MCP Config Format Comparison

**Claude Code** (`.mcp.json`):
```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "bin/simple_mcp_server",
      "args": [],
      "env": { "SIMPLE_LIB": "src", "SIMPLE_LOG": "error" }
    }
  }
}
```

**Codex CLI** (`.codex/config.toml`):
```toml
[mcp_servers.simple-mcp]
command = "bin/simple_mcp_server"
args = []
enabled = true

[mcp_servers.simple-mcp.env]
SIMPLE_LIB = "src"
SIMPLE_LOG = "error"
```

**Gemini CLI** (`.gemini/settings.json`):
```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "bin/simple_mcp_server",
      "args": [],
      "env": { "SIMPLE_LIB": "src", "SIMPLE_LOG": "error" }
    }
  }
}
```

### MCP Sharing Analysis

Claude Code and Gemini CLI use **nearly identical JSON format** (`mcpServers` key, same `command`/`args`/`env` structure). Codex CLI uses TOML with slightly different key names but same semantics.

**Shared servers (all 3 tools):** context7, simple-mcp, simple-lsp-mcp
**Gemini-only:** chrome-mcp, stitch-mcp
**Claude-only:** jj-git-mcp

### MCP CLI Commands

| Task | Claude Code | Codex CLI | Gemini CLI |
|------|-------------|-----------|------------|
| Add server | `claude mcp add <name> -s project` | `codex mcp add <name> <cmd> [args]` | `gemini mcp add <name> <cmd> [args] -s project` |
| List servers | `claude mcp list` | `codex mcp list` | `gemini mcp list` |
| Remove server | `claude mcp remove <name>` | `codex mcp remove <name>` | `gemini mcp remove <name>` |
| OAuth login | N/A | `codex mcp login <name>` | `/mcp auth <name>` |

---

## 4. Skills / Commands System

### Terminology Mapping

| Concept | Claude Code | Codex CLI | Gemini CLI |
|---------|-------------|-----------|------------|
| **Reusable prompt** | Skill (`.claude/skills/`) | Skill (`.agents/skills/` or `.codex/skills/`) | Command (`.gemini/commands/`) |
| **Slash command** | Command (`.claude/commands/`) | Slash command (built-in only) | Command (`.gemini/commands/`) |
| **Skill invocation** | `/skill-name` | `$skill-name` | `/command-name` |

### Skill/Command Locations

| Scope | Claude Code | Codex CLI | Gemini CLI |
|-------|-------------|-----------|------------|
| **Project** | `.claude/skills/` | `.agents/skills/` + `.codex/skills/` | `.gemini/commands/` |
| **User** | `~/.claude/skills/` | `~/.codex/skills/` + `~/.agents/skills/` | `~/.gemini/commands/` |
| **System** | N/A | `~/.codex/skills/.system/` (bundled) | N/A |
| **Admin** | N/A | `/etc/codex/skills/` | N/A |

### Skill Definition Format

**Claude Code** (`.claude/skills/<name>/SKILL.md` or `.claude/commands/<name>.md`):
```markdown
---
name: my-skill
description: When to trigger this skill
---

Instructions for Claude to follow.
Use $ARGUMENTS for user input.
```

**Codex CLI** (`.agents/skills/<name>/SKILL.md`):
```markdown
---
name: my-skill
description: When to trigger this skill.
---

Instructions for Codex to follow.
```
Optional `agents/openai.yaml` for UI config, tool deps, invocation policy.

**Gemini CLI** (`.gemini/commands/<name>.toml`):
```toml
description = "What this command does"
prompt = """
Instructions for Gemini to follow.
Use `$input` for arguments.
Embed shell output with !{command}.
Embed files with @{path}.
"""
```

### Skill Sharing Analysis

Claude Code and Codex CLI both use **Markdown with YAML frontmatter** (`SKILL.md`), with identical `name` + `description` fields. The instruction body is plain markdown in both. **These are structurally compatible** -- a single `SKILL.md` could work for both with minor adaptation.

Gemini CLI uses **TOML** format, which is structurally different but the prompt content is the same plain text.

**Sharing strategy:** Write skills in Markdown (SKILL.md), symlink/copy for Claude and Codex, generate TOML wrapper for Gemini.

---

## 5. Agent Definitions

### Agent Locations

| Scope | Claude Code | Codex CLI | Gemini CLI |
|-------|-------------|-----------|------------|
| **Project** | `.claude/agents/` | `[agents]` in `config.toml` | `.gemini/agents/` (experimental) |
| **User** | `~/.claude/agents/` | N/A | `~/.gemini/agents/` |

### Agent Definition Format

**Claude Code** (`.claude/agents/<name>.md`):
```markdown
---
name: code-reviewer
description: Reviews code changes
model: sonnet
tools: [Read, Grep, Glob]
---

Instructions for the agent.
```

**Codex CLI** -- agents are configured in `config.toml`:
```toml
[agents.code-reviewer]
model = "o3"
instructions = "Review code changes..."
```
Or subagent threads via `/agent` command.

**Gemini CLI** (`.gemini/agents/<name>.md`, experimental):
```markdown
---
name: code-reviewer
description: Reviews code changes
kind: local
model: gemini-2.5-pro
tools: [ReadFile, SearchFiles]
max_turns: 10
---

Instructions for the agent.
```

### Agent Sharing Analysis

Claude Code and Gemini CLI both use **Markdown with YAML frontmatter** for agent definitions. The `name`, `description`, `model`, `tools` fields are analogous. Codex uses TOML inline. Claude and Gemini agent files are structurally compatible but tool names differ.

---

## 6. Settings / Config Format

| Aspect | Claude Code | Codex CLI | Gemini CLI |
|--------|-------------|-----------|------------|
| **Format** | JSON | TOML | JSON |
| **Project file** | `.claude/settings.json` | `.codex/config.toml` | `.gemini/settings.json` |
| **User file** | `~/.claude/settings.json` | `~/.codex/config.toml` | `~/.gemini/settings.json` |
| **Local override** | `.claude/settings.local.json` | N/A (trust system) | N/A |
| **Precedence** | Managed > Local > Project > User | CLI > Profile > Project > User > System | System Override > Project > User > System Default |

---

## 7. Overlap and Conflict Analysis

### Zero-Conflict Files (completely separate namespaces)

| File/Dir | Claude | Codex | Gemini | Conflict? |
|----------|--------|-------|--------|-----------|
| `CLAUDE.md` | Read | Ignored | Ignored | None |
| `AGENTS.md` | Ignored | Read | Ignored | None |
| `GEMINI.md` | Ignored | Ignored | Read | None |
| `.claude/` | Used | Ignored | Ignored | None |
| `.codex/` | Ignored | Used | Ignored | None |
| `.gemini/` | Ignored | Ignored | Used | None |
| `.mcp.json` | Used | Ignored | Ignored | None |

### Potential Sharing Points

| Content | Can Share? | How |
|---------|-----------|-----|
| **Project instructions** | **Yes** | `CLAUDE.md` is the single source; Codex reads via `project_doc_fallback_filenames`, Gemini via `context.fileName` |
| **MCP servers** | Partially | Claude+Gemini use similar JSON; Codex uses TOML. Use a generation script |
| **Skills** | Partially | Claude+Codex both use SKILL.md format; Gemini uses TOML. Symlink or generate |
| **Agents** | Partially | Claude+Gemini both use .md with YAML frontmatter; Codex uses TOML |
| **Settings** | No | Different formats, different keys, must maintain separately |

---

## 8. Recommended Coexistence Layout

### Option A: Single Source of Truth (AGENTS.md hub)

Use `AGENTS.md` as the canonical instructions file (Codex reads natively, others import):

```
project/
  AGENTS.md                         # Canonical instructions (shared)
  CLAUDE.md                         # @AGENTS.md + Claude-specific additions
  GEMINI.md                         # @./AGENTS.md + Gemini-specific additions
  .mcp.json                         # Claude MCP servers

  .claude/
    settings.json                   # Claude permissions, hooks
    settings.local.json             # Personal Claude overrides (gitignored)
    skills/                         # Claude skills (Markdown)
    agents/                         # Claude agents (Markdown)
    commands/ -> skills/            # Symlinks for slash commands
    memory/                         # Claude memory files

  .codex/
    config.toml                     # Codex config + MCP servers (TOML)
    skills/                         # Codex skills (SKILL.md, can symlink from .claude/skills/)

  .gemini/
    settings.json                   # Gemini config + MCP servers (JSON)
    commands/                       # Gemini commands (TOML)
    agents/                         # Gemini agents (Markdown)

  config/
    mcp/
      servers.json                  # Canonical MCP server list (shared source)
      sync-mcp.sh                   # Script to generate .mcp.json, config.toml, settings.json
```

### Option B: Per-Tool Independent (no sharing, cleaner boundaries)

Each tool has fully independent config. Duplicate instructions as needed.

### Option C: Shared Skills Directory

```
project/
  .agents/                          # Shared agent skills (Codex native, others symlink)
    skills/
      verify/
        SKILL.md                    # Works for both Claude and Codex
        agents/openai.yaml          # Codex-specific UI config
      release/
        SKILL.md

  .claude/
    skills/
      verify.md -> ../../.agents/skills/verify/SKILL.md
      release.md -> ../../.agents/skills/release/SKILL.md

  .gemini/
    commands/
      verify.toml                   # Generated from SKILL.md content
      release.toml
```

---

## 9. Shared vs Tool-Specific Content Matrix

| Content Type | Shared Location | Claude-Specific | Codex-Specific | Gemini-Specific |
|-------------|-----------------|-----------------|----------------|-----------------|
| **Project rules** | `CLAUDE.md` (single source) | Native | Reads via `project_doc_fallback_filenames` | Reads via `context.fileName` |
| **Coding standards** | `CLAUDE.md` | `.claude/rules/` | `AGENTS.md` pipeline sections | `GEMINI.md` pipeline sections |
| **MCP servers** | `config/mcp/servers.json` | `.mcp.json` | `.codex/config.toml [mcp_servers]` | `.gemini/settings.json mcpServers` |
| **Skills/commands** | `.agents/skills/` (SKILL.md) | `.claude/skills/` | `.codex/skills/` + `.agents/skills/` | `.gemini/commands/` (TOML) |
| **Agents** | N/A (tool names differ) | `.claude/agents/` | `config.toml [agents]` | `.gemini/agents/` |
| **Memory** | N/A | `~/.claude/projects/*/memory/` | `~/.codex/memories/` | N/A (in-session only) |
| **Settings** | N/A | `.claude/settings.json` | `.codex/config.toml` | `.gemini/settings.json` |

---

## 10. Root Instruction File Strategy

### Recommended: Settings-Based Cross-Reading (current approach)

Each tool reads `CLAUDE.md` via its config settings — no `@` imports needed, no duplication:

```
CLAUDE.md          # Primary: comprehensive project knowledge (300+ lines)
AGENTS.md          # Codex-specific pipeline + self-sufficiency rules
GEMINI.md          # Gemini-specific pipeline + self-sufficiency rules

.codex/config.toml:
  project_doc_fallback_filenames = ["CLAUDE.md"]    # Codex reads CLAUDE.md as fallback

.gemini/settings.json:
  context.fileName = ["GEMINI.md", "AGENTS.md", "CLAUDE.md"]  # Gemini reads all three
```

**CLAUDE.md** is the single source of truth containing:
- Project structure and architecture
- Coding standards and language rules
- Test methodology and conventions
- Build commands and workflows
- Critical rules (what NOT to do)
- `.claude/skills/` skill references and `/skill-name` syntax
- `.claude/agents/` agent definitions
- jj VCS workflow
- Memory system hints

**AGENTS.md** adds Codex-specific:
- Self-sufficient pipeline steps (research → design → impl → verify → release)
- Artifact location conventions
- Codex agent/skill references

**GEMINI.md** adds Gemini-specific:
- Self-sufficient pipeline steps
- UI design emphasis (primary Gemini strength)
- `.gemini/commands/` command references
- Sandbox configuration hints

### Alternative: Hub-and-Spoke Model (not used)

Using `@` imports from a hub file. Less preferred because:
- Gemini may double-load `CLAUDE.md` if both `@` import and `context.fileName` are set
- Codex doesn't support `@` imports at all
- Settings-based approach is cleaner and more maintainable

---

## 11. MCP Server Sync Script

Since all three tools use the same MCP protocol but different config formats, a sync script can maintain consistency:

```bash
#!/bin/bash
# config/mcp/sync-mcp.sh
# Reads canonical servers.json, generates per-tool configs

SERVERS="config/mcp/servers.json"

# Generate .mcp.json (Claude Code)
jq '{mcpServers: .servers}' "$SERVERS" > .mcp.json

# Generate .gemini/settings.json mcpServers section
jq '{mcpServers: .servers}' "$SERVERS" > .gemini/settings.json.tmp
# merge with existing .gemini/settings.json...

# Generate .codex/config.toml [mcp_servers] section
# (requires json-to-toml conversion)
```

---

## 12. Feature Comparison Summary

| Feature | Claude Code | Codex CLI | Gemini CLI |
|---------|-------------|-----------|------------|
| **Instructions file** | CLAUDE.md | AGENTS.md | GEMINI.md |
| **Config format** | JSON | TOML | JSON |
| **Config dir** | `.claude/` | `.codex/` | `.gemini/` |
| **MCP support** | Yes (.mcp.json) | Yes (config.toml) | Yes (settings.json) |
| **Skills/commands** | Yes (Markdown) | Yes (SKILL.md) | Yes (TOML) |
| **Agents** | Yes (Markdown) | Yes (TOML) | Yes (Markdown, experimental) |
| **Memory system** | Yes (MEMORY.md) | Yes (memories/) | No (session only) |
| **Import syntax** | `@path` | N/A | `@./path` |
| **Override file** | N/A | AGENTS.override.md | N/A |
| **Subdirectory JIT** | Yes | Yes | Yes |
| **Nested files** | Yes (walks up) | Yes (walks up) | Yes (walks up) |
| **Cross-tool fallback** | No | Yes (configurable) | Yes (configurable) |
| **Hooks** | settings.json | hooks.json | extensions |
| **Sandbox** | N/A | Seatbelt/Docker | Dockerfile/Seatbelt |
| **Extensions** | Plugins | N/A | Extensions |
| **OAuth for MCP** | N/A | `codex mcp login` | `/mcp auth` |

---

## 13. Practical Setup for This Project

### Current State (as of 2026-03-28)

```
simple/
  CLAUDE.md              # Primary instructions (comprehensive, 300+ lines)
  AGENTS.md              # Codex-specific pipeline + tools table
  GEMINI.md              # Gemini-specific pipeline + tools table

  .claude/               # Full setup (skills, agents, memory, commands, templates)
    settings.json
    settings.local.json  # MCP: simple-mcp, simple-lsp-mcp, context7, jj-git-mcp
    skills/              # research, design, impl, verify, release (Markdown)
    agents/
    memory/
    commands/
    templates/

  .agents/skills/        # Shared skills (Codex native format, SKILL.md)
    research/SKILL.md
    design/SKILL.md
    impl/SKILL.md
    verify/SKILL.md
    release/SKILL.md

  .codex/
    config.toml          # MCP: context7, simple-mcp, simple-lsp-mcp
    skills/              # + fallback: reads CLAUDE.md
      mdsoc-architecture-writing/

  .gemini/
    settings.json        # MCP: context7, simple-mcp, simple-lsp-mcp, chrome-mcp, stitch-mcp
    commands/            # research, design, impl, verify, release (TOML)
```

### Cross-Reading Summary

| Tool | Native file | Also reads (via settings) |
|------|-------------|--------------------------|
| **Claude Code** | `CLAUDE.md` | — |
| **Codex CLI** | `AGENTS.md` | `CLAUDE.md` (fallback) |
| **Gemini CLI** | `GEMINI.md` | `CLAUDE.md` (fileName array) |

### MCP + Tools Summary

| Tool/Server | Claude | Codex | Gemini |
|-------------|--------|-------|--------|
| context7 | Yes | Yes | Yes |
| simple-mcp | Yes | Yes | Yes |
| simple-lsp-mcp | Yes | Yes | Yes |
| chrome-mcp | -- | -- | Yes |
| stitch-mcp | -- | -- | Yes |
| jj-git-mcp | Yes | -- | -- |
| Playwright CLI | -- | Yes (AGENTS.md) | Yes (GEMINI.md) |

---

## References

- [Claude Code: Memory (CLAUDE.md)](https://code.claude.com/docs/en/memory)
- [Claude Code: Settings](https://code.claude.com/docs/en/settings)
- [Claude Code: .claude/ Directory](https://code.claude.com/docs/en/claude-directory)
- [Claude Code: MCP](https://code.claude.com/docs/en/mcp)
- [Claude Code: Skills](https://code.claude.com/docs/en/skills)
- [Claude Code: Subagents](https://code.claude.com/docs/en/sub-agents)
- [Codex CLI: AGENTS.md](https://developers.openai.com/codex/guides/agents-md)
- [Codex CLI: Config](https://developers.openai.com/codex/config-basic)
- [Codex CLI: MCP](https://developers.openai.com/codex/mcp)
- [Codex CLI: Skills](https://developers.openai.com/codex/skills)
- [Gemini CLI: GEMINI.md](https://google-gemini.github.io/gemini-cli/docs/cli/gemini-md.html)
- [Gemini CLI: Config](https://google-gemini.github.io/gemini-cli/docs/get-started/configuration.html)
- [Gemini CLI: MCP](https://google-gemini.github.io/gemini-cli/docs/tools/mcp-server.html)
- [Gemini CLI: Commands](https://google-gemini.github.io/gemini-cli/docs/cli/custom-commands.html)
