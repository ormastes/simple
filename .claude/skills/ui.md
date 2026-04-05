# UI Skill — TUI/GUI Mockup Design

## Prerequisites
| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Run `/research` first |

## Stitch MCP (on-demand, GUI agent only)

Stitch MCP is **not always loaded** — start it only when Gemini UI prototyping is needed:

```bash
STITCH_API_KEY="$STITCH_API_KEY" npx -y @_davideast/stitch-mcp proxy
```

Use for Gemini-powered UI screen generation, snapshots, and interactive prototyping.

## Workflow

1. **TUI mockups** (box-drawing, ANSI colors): `doc/05_design/<feature>_tui.md`
2. **GUI mockups** (web patterns, responsive): `doc/05_design/<feature>_gui.md`
3. For Gemini GUI prototyping: start Stitch MCP (see above), then use its tools
4. Present component lists to user for confirmation

Skip if feature has no UI component.

## Outputs
| Artifact | Location |
|----------|----------|
| UI design (TUI) | `doc/05_design/<feature>_tui.md` |
| UI design (GUI) | `doc/05_design/<feature>_gui.md` |
