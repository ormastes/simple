# HTML UI Toolchain — LLM Authoring Guide

This guide is for LLM agents (and developers) authoring HTML-based UIs with the Simple HTML UI toolchain. The toolchain provides two CLIs for editing and building, a theme, and a verification oracle so you can check your work.

## What This Toolchain Is

**UI Editor (`ui_edit`)**: A command-line tool that creates and updates HTML + CSS file pairs. One HTML file can reference multiple CSS files; the editor manages all of them. Use it to scaffold new UIs, add elements, and adjust styles without manually editing HTML.

**UI Builder (`ui_build`)**: Compiles your HTML/CSS into binary UI artifacts (Simple Module Format, SMF). Two compile forms: `std` (one file with embedded parser) or `dyn` (split into a main file + parts, each < 4 KB, for embedded/constrained environments). If everything fits in the main file, only one artifact is produced.

**Core Library (`std.common.ui.html_ui`)**: The underlying toolkit. Handles HTML parsing, CSS serialization, catalog validation, and SMF code generation. You don't call it directly; the CLIs use it.

**Theme (`src/lib/common/ui/theme_html/`)**: A classless CSS theme covering all primitive UI elements (buttons, inputs, headings, tables, etc.). Simple enough to extend, designed so you style bare HTML tags—no class names needed.

## Editor Workflow (`ui_edit`)

Create and update HTML/CSS pairs using these subcommands:

| Subcommand | Invocation | Example | Notes |
|-----------|-----------|---------|-------|
| `new` | `bin/simple run src/app/ui_edit/main.spl -- new <dir>/<name>` | `bin/simple run src/app/ui_edit/main.spl -- new build/ui/dashboard` | Creates `dashboard.html` + `dashboard.css` in `build/ui/`. (DRAFT — verify file creation) |
| `list` | `bin/simple run src/app/ui_edit/main.spl -- list <name>.html` | `bin/simple run src/app/ui_edit/main.spl -- list dashboard.html` | Lists all elements and CSS files in an existing pair. |
| `add-element` | `bin/simple run src/app/ui_edit/main.spl -- add-element <name>.html <tag> [<id>]` | `bin/simple run src/app/ui_edit/main.spl -- add-element dashboard.html button submit-btn` | Adds a `<tag>` to the HTML; optional `<id>` for reference. (DRAFT — element placement rules) |
| `add-css` | `bin/simple run src/app/ui_edit/main.spl -- add-css <name>.html <path>` | `bin/simple run src/app/ui_edit/main.spl -- add-css dashboard.html styles/custom.css` | Adds a `<link rel="stylesheet" href="...">` reference to the HTML. |
| `set-css` | `bin/simple run src/app/ui_edit/main.spl -- set-css <name>.css <selector> <property> <value>` | `bin/simple run src/app/ui_edit/main.spl -- set-css dashboard.css button color #0066cc` | Updates or adds a CSS rule. (DRAFT — verify syntax and selector scope) |

**Round-trip guarantee**: Editing and re-reading preserves unrelated HTML/CSS content (verified by spec).

## Builder Workflow (`ui_build`)

Compile HTML/CSS into binary artifacts:

```bash
bin/simple run src/app/ui_build/main.spl -- build <name>.html -o build/dynsmf/ui/ --form=std|dyn
```

### Form Selection

**`--form=std`** (Standard): One SMF file embedding HTML + all CSS as base64 constants, plus runtime parsing helpers. Use when you need standalone execution with full parser support.

**`--form=dyn`** (Dynamic/Embedded): Main SMF + optional part SMFs. Main file contains element→part mapping and minimal helpers; CSS/HTML payloads are split into parts, each < 4096 bytes. Use for embedded or constrained environments.

**Merge Rule**: If total payload (HTML + CSS) fits in the main SMF after compression, only one file is produced. Otherwise, payload is split into parts ≤ 4 KB each (retry loop with shrinking chunks, max 8 iterations).

### Artifact Layout

When you run `ui_build build page.html -o build/dynsmf/ui/ --form=dyn`, the output looks like:

```
build/dynsmf/ui/
├── page.smf              (main artifact, always present)
├── page_1.smf            (part file, if payload overflows)
├── page_2.smf            (part file, if payload overflows)
└── page.uib.sdn          (manifest sidecar)
```

The `.uib.sdn` manifest records: artifact paths/sizes, element→part map, source HTML/CSS paths, form type, and catalog coverage (OK/MISSING per element).

## Verify Loop for LLMs

Use `ui_build --verify` to check that your UI is parsable and all elements are implemented:

```bash
bin/simple run src/app/ui_build/main.spl -- --verify <name>.uib.sdn
```

**Exit 0** = Success: all artifacts exist (valid `SMF\0` magic, ≥ 179 B, parts < 4096 B), and every element in the source HTML is in the catalog.

**Exit nonzero** = Failure: reads the manifest and prints per-element report:

```
OK button
OK input
MISSING custom_widget
```

**Verification contract**: This is your parse/coverage oracle. LLM agents can:
1. Author or edit HTML/CSS.
2. Run `ui_build build page.html -o /tmp/ui --form=dyn`.
3. Run `ui_build --verify <name>.uib.sdn`.
4. If nonzero, read the report, fix HTML (remove undefined elements or add to catalog), re-run steps 2–3.

**Worked Example**:

```bash
# 1. Create UI
bin/simple run src/app/ui_edit/main.spl -- new /tmp/login login
bin/simple run src/app/ui_edit/main.spl -- add-element login.html input email-field
bin/simple run src/app/ui_edit/main.spl -- add-element login.html button sign-in

# 2. Build
bin/simple run src/app/ui_build/main.spl -- build /tmp/login/login.html -o /tmp/login/out --form=dyn

# 3. Verify
bin/simple run src/app/ui_build/main.spl -- --verify /tmp/login/out/login.uib.sdn
# Output: OK input, OK button
# Exit 0

# 4. If any MISSING, fix HTML and re-run steps 2–3.
```

## Theme Usage

The default theme lives at `src/lib/common/ui/theme_html/`:

- **`simple_default.css`**: Classless stylesheet covering all primitive elements. Reference it in your HTML:
  ```html
  <link rel="stylesheet" href="src/lib/common/ui/theme_html/simple_default.css">
  ```

- **`theme_showcase.html`**: Example page showing all supported elements styled with the theme. Use it as a reference.

**Classless philosophy**: The theme styles bare HTML tags (`button`, `input`, `h1`, `p`, `table`, etc.) directly. No CSS classes needed. Add your own `<style>` or CSS files for overrides, and they will layer on top.

## TUI Subset Notes

The toolchain can degrade HTML UIs to TUI (terminal UI). CSS properties degrade as follows:

| CSS Property | HTML Behavior | TUI Degradation |
|--------------|---------------|-----------------|
| Colors (`color`, `background-color`) | Any RGB/hex | Reduced to nearest 256-color terminal palette |
| Sizes (`width`, `height`, `padding`, `margin` in `px`) | Pixel units | Converted to terminal cells (~8 px ≈ 1 cell) |
| `border-radius`, `box-shadow`, `text-shadow` | Rounded corners, shadows | Ignored (not supported in TUI) |
| `transition`, `animation` | Smooth transitions | Ignored (no animation in TUI) |
| `display: flex` (column/row) | Flexible layout | Honored (basic flex column/row supported) |
| `display: grid` | Grid layout | Unsupported; converts to block |

When authoring, avoid heavy reliance on colors, shadows, and rounded borders if TUI compatibility matters. Stick to flex layout for responsiveness.

## Element Catalog

The element catalog is auto-generated from `src/lib/common/ui/html_ui/catalog.spl`. It defines:

- Primitive tags (button, input, select, checkbox, radio, textarea, label, heading, paragraph, list, table, image, container, nav/menu)
- Widget kind (form control, container, semantic, media, etc.)
- TUI degradation notes per element

The verify mode checks that every `<tag>` in your HTML is in this catalog. To add support for a new element, edit `catalog.spl` and re-run the verification loop.

*Catalog table (placeholder — generated at spec time):*

| Tag | Widget Kind | TUI Note |
|-----|-------------|----------|
| `button` | Form Control | Text-only; no color/shadow |
| `input` | Form Control | TUI: reduced to type hints |
| `select` | Form Control | TUI: renders as input fallback |
| ... | ... | ... |

(Full table at `src/lib/common/ui/html_ui/catalog.spl`.)

## Next Steps

- **For new UIs**: Start with `bin/simple run src/app/ui_edit/main.spl -- new ...`, add elements, build, and verify.
- **For existing HTML**: Use `ui_build build <file>.html --form=dyn`, verify with `--verify`, and iterate.
- **For TUI**: Author UIs avoiding heavy colors/shadows; test with TUI render path.
- **For customization**: Add CSS files with `add-css`, and override theme rules in your own stylesheets.
