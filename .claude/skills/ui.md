# UI Skill — TUI/GUI Mockup Design

## Prerequisites
| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Run `/research` first |
| Design system reference | `doc/05_design/stitch_design_system.md` | Extract from Stitch MCP |

## Stitch MCP — Google's AI UI Design Tool

**What it is:** Stitch is a Google MCP service that uses Gemini to generate HTML/CSS UI screens from text prompts. It manages design systems (colors, fonts, spacing, roundness) and generates desktop/mobile/tablet screens that follow those systems. Output is production-quality HTML+CSS.

**Key capabilities:**
- `create_design_system` / `update_design_system` — define color palette, fonts, roundness, spacing, and a free-form `designMd` markdown that teaches Gemini the visual language
- `generate_screen_from_text` — generate a full screen from a text prompt (1-3 min per screen)
- `edit_screens` — modify existing screens with focused prompts
- `generate_variants` — create layout/color/typography variants of existing screens
- `apply_design_system` — re-skin screens to match a design system
- `get_screen` — retrieve generated HTML/CSS code

**Design system reference:** All SimpleOS design systems (Obsidian dark, Celestial Ether light, Glass original) are documented with full token tables, component specs, and Stitch API configuration in:
> **[`doc/05_design/stitch_design_system.md`](doc/05_design/stitch_design_system.md)**

**Existing Stitch projects:**
- Project `12496218458601315145` — "Simple OS UI" (Obsidian + Celestial Ether design systems, 17 screens)
- Project `14134637940805933672` — "SimpleOS Glass" (original Glass design system, 19 screens)

**Start Stitch MCP (if not already loaded):**
```bash
STITCH_API_KEY="$STITCH_API_KEY" npx -y @_davideast/stitch-mcp proxy
```

## Workflow

1. **TUI mockups** (box-drawing, ANSI colors): `doc/05_design/<feature>_tui.md`
2. **GUI mockups** (web patterns, responsive): `doc/05_design/<feature>_gui.md`
3. For Gemini GUI prototyping: start Stitch MCP, then use its tools
4. For theme consistency: read `doc/05_design/stitch_design_system.md` for tokens, components, and DO/DON'T rules
5. Present component lists to user for confirmation

Skip if feature has no UI component.

## Minimal Screen Set for Theme Validation

When creating a new theme, generate at minimum:
1. **Desktop / Launcher** — system bar, dock, gradient background
2. **Window Manager (3 windows)** — chrome, focus/inactive, overlapping shadows
3. **Settings Panel** — sidebar nav, cards, toggles, nested glass
4. **File Manager** — toolbar, sidebar, grid/list views, search

Full coverage (10 screens) documented in `stitch_design_system.md` Section 9.

## Outputs
| Artifact | Location |
|----------|----------|
| UI design (TUI) | `doc/05_design/<feature>_tui.md` |
| UI design (GUI) | `doc/05_design/<feature>_gui.md` |
| Design system ref | `doc/05_design/stitch_design_system.md` |
