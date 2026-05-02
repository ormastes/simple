# UI Design Skill — Gemini-Powered TUI/GUI Mockup Generation

**Step 3 of Cooperative Pipeline.** This skill generates TUI and GUI mockup designs using Google Gemini CLI. It reads requirements produced in Steps 1-2 and produces visual mockups for implementation in Steps 4-5.

## Prerequisites

| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Run `/research` first |
| Gemini CLI | `gemini` binary in PATH | Install: `npm install -g @anthropic-ai/gemini-cli` or equivalent |
| Stitch MCP (optional) | `.mcp.json` stitch entry | Add via `claude mcp add` for HTML generation |

## Usage

```
/gemini-ui-design <feature>           # Generate TUI + GUI mockups for feature
/gemini-ui-design <feature> --tui     # TUI mockup only
/gemini-ui-design <feature> --gui     # GUI mockup only
/gemini-ui-design <feature> --html    # Generate production HTML via Stitch
```

Argument: `$ARGUMENTS`

---

## Workflow

### Phase 1 — Requirement Ingestion

1. Read `doc/02_requirements/feature/<feature>.md`
2. Extract UI-relevant requirements:
   - User-facing interactions (inputs, outputs, displays)
   - Data to visualize (tables, charts, metrics)
   - Navigation flows (screens, transitions)
   - Accessibility requirements
3. If no requirements doc exists, ask user for feature description

### Phase 2 — TUI Mockup Design

Generate terminal UI mockups using box-drawing characters and ANSI formatting:

1. **Layout structure** — Define screen regions (header, sidebar, main, footer)
2. **Component inventory** — List all UI components needed:
   - Input fields, buttons, toggles, dropdowns
   - Tables, lists, tree views
   - Status bars, progress indicators
   - Dialog boxes, modals
3. **Box-drawing mockup** — Create ASCII art layout:
   ```
   +--[ Feature Dashboard ]---------------------------+
   | [Nav] | Metrics          | Actions               |
   |-------+------------------+-----------------------|
   | > Home| CPU: ████░ 78%   | [Start] [Stop] [Reset]|
   | > Logs| Mem: ██░░░ 42%   |                       |
   | > Set | Disk: █████ 95%  | Status: Running       |
   +--------------------------------------------------+
   ```
4. **Color scheme** — Specify ANSI colors for emphasis, status, errors
5. **Interaction flow** — Document keyboard navigation (Tab, Enter, Esc, arrows)

Output to: `doc/05_design/<feature>_tui.md`

### Phase 3 — GUI Mockup Design

Generate web GUI mockups using responsive design patterns:

1. **Layout grid** — Define responsive breakpoints and grid structure
2. **Component library** — Map to standard web components:
   - Forms, inputs, buttons (primary/secondary/danger)
   - Cards, panels, accordions
   - Data tables with sort/filter
   - Charts (bar, line, pie)
   - Navigation (sidebar, tabs, breadcrumbs)
3. **Visual mockup description** — Structured layout specification:
   ```
   Header: Logo left, user menu right, search center
   Sidebar: 200px fixed, collapsible, icon + label nav items
   Main: 2-column grid (metrics cards top, detail table bottom)
   Footer: Status bar with connection indicator
   ```
4. **Responsive behavior** — Mobile, tablet, desktop variants
5. **Interaction patterns** — Click, hover, drag, keyboard shortcuts

Output to: `doc/05_design/<feature>_gui.md`

### Phase 4 — HTML Generation (optional, with Stitch)

If `--html` flag is set and Stitch MCP is available:

1. Use `mcp__stitch__build_site` to generate production HTML/CSS
2. Use `mcp__stitch__get_screen_code` to retrieve individual screen code
3. Place generated HTML in `examples/<feature>/` or `src/app/web/`
4. Ensure responsive design, semantic HTML, ARIA accessibility

### Phase 5 — Component Confirmation

Present to user for confirmation:
- Component inventory list
- Screen flow diagram
- Color/theme choices
- Interaction patterns

---

## Gemini CLI Integration

When Gemini CLI is available, use it for enhanced design generation:

```bash
# Generate mockup via Gemini
gemini -p "Design a TUI layout for <feature> with these requirements: ..."

# Generate HTML component
gemini -p "Create an HTML/CSS component for <component> with responsive design"
```

### Gemini Prompting Guidelines

- Include specific requirements from the feature doc
- Specify target framework (vanilla HTML/CSS, or Simple web templates)
- Request box-drawing characters for TUI, semantic HTML for GUI
- Ask for accessibility attributes (ARIA, keyboard nav)
- Include color palette constraints if project has a design system

---

## Design Guidelines

- Generate clean, semantic HTML with minimal inline styles
- Prefer CSS classes over inline styles for reusability
- Use responsive design patterns (flexbox/grid)
- Keep accessibility in mind (ARIA labels, semantic tags, contrast)
- When integrating with Simple projects, output to `.spl` web templates or standalone HTML
- TUI mockups must work in 80-column terminals minimum
- GUI mockups must include mobile-first responsive breakpoints

## Outputs

| Artifact | Location |
|----------|----------|
| UI design (TUI) | `doc/05_design/<feature>_tui.md` |
| UI design (GUI) | `doc/05_design/<feature>_gui.md` |
| HTML prototype | `examples/<feature>/index.html` (if --html) |
| Component list | Included in design docs |

## Cooperative Pipeline Context

```
Step 1: Claude /research  →  Step 2: Codex $research  →  Step 3: Gemini /design (UI) ← THIS SKILL
→  Step 4: Codex $design (arch)  →  Step 5: Claude /design (quality)
```

This skill consumes outputs from Steps 1-2 and produces inputs for Steps 4-5. The requirements doc and research notes guide the UI design. The produced mockups inform architecture decisions (Step 4) and quality validation (Step 5).
