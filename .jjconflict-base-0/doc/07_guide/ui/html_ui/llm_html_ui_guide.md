# HTML UI Toolchain — LLM Authoring Guide

This guide is for LLM agents (and developers) authoring HTML-based UIs with the Simple HTML UI toolchain. The toolchain provides two CLIs for editing and building, a theme, and a verification oracle so you can check your work.

## What This Toolchain Is

**UI Editor (`ui_edit`)**: A command-line tool that creates and updates HTML + CSS file pairs. One HTML file can reference multiple CSS files; the editor manages all of them. Use it to scaffold new UIs, add elements, and adjust styles without manually editing HTML.

**UI Builder (`ui_build`)**: Compiles your HTML/CSS into binary UI artifacts (Simple Module Format, SMF). Two compile forms: `std` (one file with embedded parser) or `dyn` (split into a main file + parts, each < 4 KB, for embedded/constrained environments). If everything fits in the main file, only one artifact is produced.

**Core Library (`std.common.ui.html_ui`)**: The underlying toolkit. Handles HTML parsing, CSS serialization, catalog validation, and SMF code generation. You don't call it directly; the CLIs use it.

**Theme (`src/lib/common/ui/theme_html/`)**: A classless CSS theme (7783 B, `simple_default.css`) covering all primitive UI elements (buttons, inputs, headings, tables, etc.). Styles bare HTML tags — no class names needed. Includes dark-mode support via `@media (prefers-color-scheme: dark)`.

## Editor Workflow (`ui_edit`)

Create and update HTML/CSS pairs using these subcommands:

| Subcommand | Invocation | Example |
|-----------|-----------|---------|
| `new` | `bin/simple run src/app/ui_edit/main.spl -- new <dir>/<name>` | `bin/simple run src/app/ui_edit/main.spl -- new /tmp/ui/dashboard` |
| `list` | `bin/simple run src/app/ui_edit/main.spl -- list <page.html>` | `bin/simple run src/app/ui_edit/main.spl -- list /tmp/ui/dashboard.html` |
| `add-element` | `bin/simple run src/app/ui_edit/main.spl -- add-element <page.html> <tag> [--id=X] [--parent=TAG] [--text=...]` | `bin/simple run src/app/ui_edit/main.spl -- add-element /tmp/ui/dashboard.html button --id=submit-btn --text="Submit"` |
| `add-css` | `bin/simple run src/app/ui_edit/main.spl -- add-css <page.html> <styles.css>` | `bin/simple run src/app/ui_edit/main.spl -- add-css /tmp/ui/dashboard.html /tmp/ui/custom.css` |
| `set-css` | `bin/simple run src/app/ui_edit/main.spl -- set-css <page.html> <styles.css> <selector> <property> <value>` | `bin/simple run src/app/ui_edit/main.spl -- set-css /tmp/ui/dashboard.html /tmp/ui/dashboard.css button color "#0066cc"` |
| `help` | `bin/simple run src/app/ui_edit/main.spl -- help` | Shows usage and exits 0 |

**Notes**:
- `new <dir>/<name>` creates `<dir>/<name>.html` and `<dir>/<name>.css` (both files, not inside a subdirectory).
- `add-element` flags are named: `--id=X`, `--parent=TAG`, `--text=...`. The tag must be in the element catalog.
- `set-css` takes the HTML path first, then the CSS path, then `<selector> <property> <value>`. It sets or appends a single property in a selector block (text-level rewrite; one property per call — see Known Limitations).
- `add-css` injects a `<link rel="stylesheet" href="...">` before `</head>`, using a relative href if the CSS is in the same directory as the HTML.

**Round-trip guarantee**: Editing and re-reading preserves unrelated HTML/CSS content (verified by spec).

**Real output** (verified):
```
Created: /tmp/ui_guide_test/login.html
Created: /tmp/ui_guide_test/login.css

Added <input> to /tmp/ui_guide_test/login.html
Added <button> to /tmp/ui_guide_test/login.html

Set button { color: #0066cc; } in /tmp/ui_guide_test/login.css
```

## Builder Workflow (`ui_build`)

Compile HTML/CSS into binary artifacts:

```bash
bin/simple run src/app/ui_build/main.spl -- build <page.html> -o <outdir> [--form=std|dyn]
```

### Form Selection

**`--form=std`** (Standard): One SMF file embedding HTML + all CSS as base64 constants, plus runtime parsing helpers. Use when you need standalone execution with full parser support.

**`--form=dyn`** (Dynamic/Embedded): Main SMF + optional part SMFs. Main file contains element→part mapping and minimal helpers; CSS/HTML payloads are split into parts, each < 4096 bytes. Use for embedded or constrained environments.

**Merge Rule**: If total payload (HTML + CSS) fits in the main SMF after compression, only one file is produced. Otherwise, payload is split into parts ≤ 4 KB each (retry loop with shrinking chunks, max 8 iterations).

### Artifact Layout

When you run `bin/simple run src/app/ui_build/main.spl -- build page.html -o /tmp/ui --form=dyn`, the output looks like:

```
/tmp/ui/
├── page.smf              (main artifact, always present — currently a 219-byte stub; see Known Limitations)
├── page_part_0.smf       (part file, if payload overflows)
├── page_part_1.smf       (part file, if payload overflows)
├── page.uib.sdn          (manifest sidecar)
└── gen/
    └── page_dyn_main.spl (generated source — this is where the payload lives)
```

The `.uib.sdn` manifest records: artifact paths/sizes, element→part map, source HTML/CSS paths, form type, and catalog coverage. Verify reads this manifest.

## Verify Loop for LLMs

Use `ui_build verify` to check that your UI is parsable and all elements are implemented:

```bash
bin/simple run src/app/ui_build/main.spl -- verify <name>.uib.sdn
```

(`--verify` is also accepted as an alias for `verify`.)

**Exit 0** = all artifacts exist (size ≥ 179 B), every element in the source HTML is either in the catalog or in the known-passthrough meta-tag list, and the verify prints `PASS`.

**Exit nonzero** = prints a per-element report and no `PASS` line.

**Verification contract**: This is your parse/coverage oracle. LLM agents should:
1. Author or edit HTML/CSS.
2. Run `ui_build build page.html -o /tmp/ui --form=dyn`.
3. Run `ui_build verify /tmp/ui/page.uib.sdn`.
4. Parse stdout for `PASS` or `MISSING <tag>` lines. Do not rely solely on exit code (see Known Limitations).
5. If any `MISSING`, remove the undefined element from HTML or add it to `catalog.spl`, then re-run steps 2–4.

**Worked Example** (real output from `theme_showcase.html`):

```bash
# 1. Build
bin/simple run src/app/ui_build/main.spl -- build \
  src/lib/common/ui/theme_html/theme_showcase.html \
  -o /tmp/ui_build_test --form=dyn

# Real stdout:
# ui_build: building 'theme_showcase' form=dyn -> /tmp/ui_build_test
#   compiling dyn merged attempt...
#   merged build fits: /tmp/ui_build_test/theme_showcase.smf (219 bytes)
#   manifest: /tmp/ui_build_test/theme_showcase.uib.sdn

# 2. Verify
bin/simple run src/app/ui_build/main.spl -- verify \
  /tmp/ui_build_test/theme_showcase.uib.sdn

# Real stdout (trimmed):
# ui_build verify: /tmp/ui_build_test/theme_showcase.uib.sdn
# OK artifact: /tmp/ui_build_test/theme_showcase.smf (219 bytes, main)
# OK html
# OK body
# OK header
# OK nav
# OK main
# ... (one OK line per catalog element found in the HTML)
# OK progress
# OK footer
# PASS
```

## Theme Usage

The default theme lives at `src/lib/common/ui/theme_html/`:

- **`simple_default.css`** (7783 B): Classless stylesheet. Styles ~50+ bare HTML tags with CSS variables, flexbox nav, and dark-mode support (`@media (prefers-color-scheme: dark)`). No class selectors. Reference it in your HTML:
  ```html
  <link rel="stylesheet" href="src/lib/common/ui/theme_html/simple_default.css">
  ```

- **`theme_showcase.html`** (257 lines, 49 tagged elements): Example page showing all supported elements. Use it as a build/verify reference.

**Classless philosophy**: The theme styles bare HTML tags directly. Add your own `<style>` or additional CSS files for overrides; they layer on top.

## TUI Subset Notes

The toolchain can degrade HTML UIs to TUI (terminal UI). CSS properties degrade as follows:

| CSS Property | HTML Behavior | TUI Degradation |
|--------------|---------------|-----------------|
| Colors (`color`, `background-color`) | Any RGB/hex | Reduced to nearest 256-color terminal palette |
| Sizes (`width`, `height`, `padding`, `margin` in `px`) | Pixel units | Converted to terminal cells (~8 px ≈ 1 cell) |
| `border-radius`, `box-shadow`, `text-shadow` | Rounded corners, shadows | Ignored |
| `transition`, `animation` | Smooth transitions | Ignored |
| `display: flex` (column/row) | Flexible layout | Honored (basic flex column/row supported) |
| `display: grid` | Grid layout | Unsupported; converts to block |

When authoring, avoid heavy reliance on colors, shadows, and rounded borders if TUI compatibility matters. Stick to flex layout for responsiveness.

## Element Catalog

Source: `src/lib/common/ui/html_ui/catalog.spl`. The verify command rejects any `<tag>` not in this catalog (or the meta-tag passthrough list). 51 entries:

| Tag | Widget Kind | TUI Note |
|-----|-------------|----------|
| `html` | panel | root container; ignore in TUI |
| `body` | panel | root container; ignore in TUI |
| `div` | panel | generic container |
| `section` | panel | semantic section |
| `article` | card | card-like block |
| `aside` | sidebar | sidebar panel |
| `main` | panel | main content area |
| `header` | panel | header bar; map to statusbar in TUI |
| `footer` | statusbar | footer / status bar |
| `nav` | navigation_bar | navigation bar |
| `h1` | heading | top-level heading |
| `h2` | heading | heading level 2 |
| `h3` | heading | heading level 3 |
| `h4` | heading | heading level 4 |
| `h5` | heading | heading level 5 |
| `h6` | heading | heading level 6 |
| `p` | text | paragraph text |
| `span` | text | inline text |
| `ul` | list | unordered list |
| `ol` | list | ordered list |
| `li` | text | list item |
| `table` | table | table widget |
| `thead` | panel | table header group |
| `tbody` | panel | table body group |
| `tfoot` | panel | table footer group |
| `tr` | panel | table row |
| `th` | text | table header cell |
| `td` | text | table data cell |
| `caption` | text | table caption |
| `button` | button | button |
| `input` | input | input; type=checkbox→checkbox, type=radio→radio, else textfield |
| `select` | dropdown | dropdown selector |
| `option` | text | dropdown option item |
| `textarea` | textarea | multi-line text input |
| `label` | label | form label |
| `form` | panel | form container |
| `fieldset` | panel | grouped form fields |
| `legend` | text | fieldset caption |
| `img` | image | image; TUI shows alt text |
| `a` | text | hyperlink; TUI shows as text |
| `blockquote` | panel | block quote |
| `code` | text | inline code |
| `pre` | text | preformatted text block |
| `strong` | text | bold inline |
| `em` | text | italic inline |
| `hr` | divider | horizontal rule |
| `details` | panel | disclosure widget |
| `summary` | text | details summary / toggle label |
| `dialog` | dialog | modal dialog |
| `progress` | progress | progress bar |

**Meta-tag passthrough**: Tags in the following list pass catalog checks unconditionally (build does not fail if they appear in HTML): `html`, `head`, `meta`, `title`, `link`, `script`, `style`, `noscript`, `base`, `small`, `br`, `wbr`, `abbr`, `cite`, `dfn`, `kbd`, `samp`, `var`, `mark`, `time`, `sub`, `sup`, `i`, `b`, `u`, `s`, `del`, `ins`, `q`, `address`, `bdo`, `bdi`, `figure`, `figcaption`, `map`, `area`, `track`, `source`, `video`, `audio`. Note: many of these also appear as `OK` lines in verify output even though they are not in the catalog.

## Known Limitations

### (a) SMF artifacts are 219-byte stubs

The compiler currently emits stub `.smf` files that do **not** embed the module payload. The real payload-bearing artifact is the generated `.spl` module written to `<outdir>/gen/` (e.g. `gen/page_dyn_main.spl`). The verify command checks artifact existence and size (≥ 179 B), and the stub satisfies that threshold, so verify passes. However, `--strict` mode (if added) would fail on stubs. When consuming artifacts downstream, read from the `gen/` directory, not the `.smf` file.

Reference: `doc/08_tracking/bug/` — see `serialization_smf_stub_only_no_spl_source_2026-05-30.md` for the upstream stub issue.

### (b) Interpreter exit codes are unreliable

In interpreter mode (the default `bin/simple run` invocation), exit codes can be unreliable depending on interpreter version. **LLM agents must parse stdout** rather than relying on the process exit code:
- A successful verify prints `PASS` on its own line.
- A failed verify prints one or more `MISSING <tag>` lines and does **not** print `PASS`.
- Parse these lines, not the exit code.

### (c) `set-css` is text-level, one property per call

`set-css` rewrites CSS at text level. It sets or appends exactly **one** CSS property per invocation. To set multiple properties on a selector (e.g. `button { color: ...; background: ...; }`), call `set-css` once per property. It preserves all unrelated CSS content.

## Next Steps

- **For new UIs**: Start with `bin/simple run src/app/ui_edit/main.spl -- new ...`, add elements, build, and verify.
- **For existing HTML**: Run `bin/simple run src/app/ui_build/main.spl -- build <file>.html -o <outdir> --form=dyn`, then `verify`, and iterate on MISSING lines.
- **For TUI**: Author UIs avoiding heavy colors/shadows; test with TUI render path.
- **For customization**: Add CSS files with `add-css`, then override theme rules with `set-css` (one property per call).
- **For new elements**: Add an entry to `src/lib/common/ui/html_ui/catalog.spl` and re-run the verify loop.
