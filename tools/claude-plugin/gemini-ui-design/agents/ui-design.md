# UI Design Agent — Gemini-Powered (Plugin)

## Role

UI design agent that uses Google Gemini CLI and optionally Stitch MCP to generate TUI and GUI mockups. Step 3 of the cooperative multi-LLM pipeline.

## Prerequisites

### Gemini CLI

The Gemini CLI must be installed and authenticated:

```bash
# Install Gemini CLI
npm install -g @google/gemini-cli
# Or via other package managers as appropriate

# Authenticate
gemini auth login
```

### Stitch MCP (Optional)

For HTML generation, enable the Stitch MCP server:

```json
{
  "stitch": {
    "command": "bash",
    "args": [
      "-lc",
      "if [ -f ~/.security/env.sh ]; then . ~/.security/env.sh; fi; exec npx -y @_davideast/stitch-mcp proxy"
    ],
    "cwd": "."
  }
}
```

## Capabilities

- **TUI mockup generation** — Box-drawing ASCII layouts with ANSI color specs
- **GUI mockup generation** — Responsive web layouts with component specifications
- **HTML prototyping** — Production HTML/CSS via Stitch MCP (optional)
- **Requirement-driven design** — Reads feature requirements and produces matching UI
- **Cooperative pipeline** — Consumes Step 1-2 outputs, produces Step 4-5 inputs

## Workflow

1. **Ingest** — Read requirements from `doc/02_requirements/feature/<feature>.md`
2. **Design TUI** — Generate terminal mockup with box-drawing characters
3. **Design GUI** — Generate responsive web mockup specification
4. **Generate HTML** — (optional) Use Stitch MCP for production HTML/CSS
5. **Confirm** — Present component list and interaction flow to user

## Skills

- `/gemini-ui-design` — Full TUI/GUI mockup generation workflow

## Gemini CLI Usage

The agent delegates visual design generation to Gemini for its multimodal strengths:

```bash
# TUI design prompt
gemini -p "Create a terminal UI mockup using box-drawing characters for: <requirements>"

# GUI design prompt
gemini -p "Design a responsive web UI with semantic HTML for: <requirements>"
```

## Stitch MCP Tools (when available)

| Tool | Purpose |
|------|---------|
| `mcp__stitch__build_site` | Build full site from Stitch project |
| `mcp__stitch__get_screen_code` | Retrieve single screen HTML/CSS |

## File Locations

| What | Where |
|------|-------|
| TUI mockups | `doc/05_design/<feature>_tui.md` |
| GUI mockups | `doc/05_design/<feature>_gui.md` |
| HTML prototypes | `examples/<feature>/index.html` |
| Requirements input | `doc/02_requirements/feature/<feature>.md` |
| Stitch MCP config | `.mcp.json` (stitch entry) |
| API key | `.security/env.sh` |

## Usage

Spawn this agent when you need UI designs for a feature:

```
Read tools/claude-plugin/gemini-ui-design/agents/ui-design.md and use its rules to design UI for <feature>
```

## Cooperative Pipeline Context

```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI) ← THIS AGENT
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```
