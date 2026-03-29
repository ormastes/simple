# UI Design Agent — Stitch MCP Integration

## MCP Servers

This agent requires the following MCP server (not loaded by default — enable when spawning UI design tasks):

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

**Enable before use:** Add to `.mcp.json` or run `claude mcp add` when working on UI design tasks.

**Use when:** Designing UI screens, generating HTML/CSS components, creating layouts, prototyping interfaces, or converting design descriptions into production-ready HTML.

**Skills:** `/design`

## Stitch MCP Tools

This agent uses Google Stitch via the `stitch` MCP server to generate and retrieve UI designs.

### Available MCP Tools

| Tool | Purpose |
|------|---------|
| `mcp__stitch__build_site` | Build a full site from a Stitch project — maps screens to routes, returns design HTML per page |
| `mcp__stitch__get_screen_code` | Retrieve a single screen's HTML/CSS code from Stitch |

### Workflow

1. **Describe** — User provides a UI description (layout, components, style)
2. **Generate** — Use Stitch MCP to generate the design as production HTML/CSS
3. **Retrieve** — Fetch screen code with `get_screen_code`
4. **Integrate** — Place generated HTML into the project (e.g., `src/app/web/`, `examples/`)
5. **Refine** — Iterate on the design based on user feedback

### Environment

- **API Key:** `STITCH_API_KEY` — loaded from `.security/env.sh` (never committed)
- **MCP Server:** `stitch` entry in `.mcp.json` — runs `@_davideast/stitch-mcp proxy`

### Design Guidelines

- Generate clean, semantic HTML with minimal inline styles
- Prefer CSS classes over inline styles for reusability
- Use responsive design patterns (flexbox/grid)
- Keep accessibility in mind (ARIA labels, semantic tags, contrast)
- When integrating with Simple projects, output to `.spl` web templates or standalone HTML

### Example Prompts

```
"Design a dashboard with sidebar nav, metrics cards, and a chart area"
"Create a login page with email/password fields and social auth buttons"
"Build a settings page with toggle switches and a save button"
```

### File Locations

| What | Where |
|------|-------|
| Stitch MCP config | `.mcp.json` (stitch entry) |
| API key | `.security/env.sh` |
| Web app templates | `src/app/web/` |
| Example outputs | `examples/` |
| Design docs | `doc/05_design/` |
