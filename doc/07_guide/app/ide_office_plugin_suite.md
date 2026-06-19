# IDE Office Plugin Suite Guide

The IDE Office plugin suite exposes Markdown, slides, Draw/SDD diagrams,
sheets, dashboard, DB admin, and LibreOffice-like app catalog checks through
`src/app/ide/feature_report.spl`.

## Canonical Surfaces

- Markdown WYSIWYG model: `src/app/office/md_wysiwyg.spl`
- Markdown GUI render entry: `src/app/office/md_wysiwyg_gui.spl`
- Writer Markdown render: `src/app/office/word/html_render.spl`
- Office headless action bridge: `src/app/office/mod.spl`
- IDE Markdown probe: `src/app/ide/markdown_render.spl`
- Slide/PPT HTML render: `src/app/office/slides/html_render.spl`
- IDE slide probe: `src/app/ide/slides_compat.spl`
- IDE Draw probe: `src/app/ide/draw_sanity.spl`
- HTML UI editor: `src/app/office/ui_editor.spl`
- Game data bridge: `src/app/office/game_bridge.spl`
- SDD diagram substrate: `src/lib/editor/services/sdn_graph.spl`
- LLM-readable catalog: `src/app/office/llm_catalog.spl`
- IDE system spec:
  `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`

## Rendering Contract

Markdown is the product source format for both Writer and PPT/Impress. HTML is
the generated render target.

Markdown GUI rendering must use `wysiwyg_preview_document_html`, not a bare
preview pane. The document helper owns the stable `.wysiwyg-preview` CSS wrapper
and the escaped styled HTML generated from source lines.

Writer rendering must expose Markdown source -> paper/document HTML through
`render_writer_markdown_html`.

PPT/Impress rendering must expose Markdown source -> slide-deck HTML through
`render_ppt_markdown_html`. The object-model slide renderer remains a
compatibility path and should escape element text, sanitize CSS colors to simple
`#RGB` or `#RRGGBB` values, clamp negative geometry to `0px`, and emit a fixed
960x540 relative slide with absolutely positioned element boxes.

Headless Office actions are exposed through
`office_action_dispatch(action, source)` in `app.office.mod`. This is the stable
non-GUI bridge for cataloged render/export actions:
`render-writer-markdown-html`, `render-ppt-markdown-html`, `render-ui-html`,
`export-ui-sdd`, and `render-sdd-html-with-selection`. The bridge delegates to
the canonical Writer, Impress, Designer, and SDD renderers rather than
duplicating rendering logic.

Designer/UI editing uses `app.office.ui_editor` as a pure HTML design document
substrate. It parses positioned frame/component records, renders a stable
`.office-ui-design` HTML surface with inspector metadata, exports nodes to
SDD-compatible tables, and guards label/layout/layer edits with expected-value
checks. Numeric layer values render as deterministic `data-z-index` / CSS
`z-index` values; semantic layer names fall back to document-order stack values.
Selection and inspection are read-only derived views: selected renders add
`data-selected`/`aria-selected` metadata, and `ui-inspect-node` returns a node
snapshot without mutating the design document. Style-token reads and guarded
style-token edits expose the node `css` token as a deterministic visual class;
they do not accept arbitrary CSS blocks. Multi-node alignment and distribution
use geometry signatures as stale-selection guards and remain integer-only,
all-or-nothing edits over selected nodes. Frame-level auto-layout resolves
horizontal/vertical child placement from integer gap/padding metadata, and
parent/constraint edits materialize deterministic Figma-like child geometry
without delegating to a browser layout engine.

Draw/diagram editing should prefer the SDD substrate in
`std.editor.services.sdn_graph` for geometry, layers, connector routes,
waypoints, anchors, rendered SVG connector paths, pure edge reroute operations,
parent/group metadata, transient selection rendering, pure node/edge inspector
snapshots, pure node shape/style/parent edit operations, and canvas/page
metadata. `src/app/ide/draw_sanity.spl` is the product feature-check bridge:
it proves render, selection, inspection, reroute, node edit, and canvas metadata
without starting GUI/browser/host APIs. Legacy SVG shape helpers remain
compatibility utilities, not the LLM catalog owner for Draw.

Calc formula hardening should distinguish display-safe functions from the
f64-returning formula path. `evaluate_formula_display_text` is the verified path
for runner-stable COUNTA, exact-match VLOOKUP, and text functions (`LEN`,
`LOWER`, `UPPER`, `TRIM`). `SheetsApp.confirm_edit()` stores supported
display-safe results into formula `cached_display` so the visible grid renders
those values after app-level recalc; full numeric formula parity remains gated
on the tracked f64 backend blocker.

Base editing uses `app.office.base_db` as a pure text-table substrate. Checked
row insertion validates schema width before appending, while `update_where`,
`delete_where`, and `count_where` apply exact-match predicates without
filesystem, SQL parser, or GUI dependencies. These helpers preserve the
iteration-based row access workaround used for non-first columns.

Game tool integration uses `app.office.game_bridge` as a pure data bridge over
Calc, Draw, and Base. Calc cell references become level/tuning tokens, SDD Draw
nodes become deterministic sprite records, and Base exact-match query rows
become `key=value` game state records. The bridge does not import a game loop,
GUI renderer, browser, filesystem, or host API.

Math editing uses `app.office.math_editor` as a pure MathML rendering substrate.
The public renderer keeps flat token MathML for simple expressions, escapes
XML-sensitive operator text, and recognizes `frac(a, b)` shorthand for the same
fraction form used by the VS Code math preview. Structured helpers expose
fractions, superscripts, subscripts, square roots, and fenced groups without a
browser or CAS dependency. `math_to_mathml_checked` adds bounded checked
rendering for core precedence (`^`, `*`, `/`, `+`, `-`), parentheses,
`sqrt(...)`, and malformed-input fallback reasons.

IDE feature checks should expose these hardening markers in both TUI and GUI
modes:

- Markdown: `css_doc=true escaped=true`
- Slides: `ppt_html=true safe_css=true positioned=true`
- Draw: `html=true route=true select=true inspect=true edit=true canvas=true`
- LLM catalog: Writer has `render-writer-markdown-html`; Impress has
  `render-ppt-markdown-html`; Draw is SDD-backed with
  `render-sdd-html-with-selection`, `reroute-sdd-connector`,
  `edit-sdd-node-parent`, `edit-sdd-node-shape`, `edit-sdd-node-style`,
  `edit-sdd-canvas`, `inspect-sdd-node`, and `inspect-sdd-edge`; Calc has `formula-counta`,
  `formula-text-functions`, `formula-vlookup`, and
  `formula-display-recalc`; Base has `schema-validation`, `count-where`,
  `update-where`, `delete-where`, and `db-edit`; Math has `fraction`,
  `subscript`, `fenced-group`, `precedence-parser`, `checked-rendering`,
  `render-math-structure`, and `render-mathml-checked`; Designer has
  `render-ui-html`, `export-ui-sdd`, and
  `ui-label-edit` / `ui-layout-edit` / `ui-auto-layout-edit` /
  `ui-constraints-edit` / `ui-align-selection` /
  `ui-distribute-selection` / `ui-layer-edit` /
  `ui-style-token-read` / `ui-style-token-edit` / `ui-inspect-node`.

## Verification

Run each focused gate once per session:

```sh
bin/simple check \
  src/app/office/md_wysiwyg.spl \
  src/app/office/md_wysiwyg_gui.spl \
  src/app/office/slides/html_render.spl \
  src/app/office/ui_editor.spl \
  src/app/office/game_bridge.spl \
  src/app/ide/markdown_render.spl \
  src/app/ide/slides_compat.spl \
  test/01_unit/app/office/md_wysiwyg_spec.spl \
  test/01_unit/app/office/md_wysiwyg_render_spec.spl \
  test/01_unit/app/office/slides/html_render_spec.spl \
  test/01_unit/app/office/ui_editor_spec.spl \
  test/01_unit/app/office/game_bridge_spec.spl \
  test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl

SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/slides/html_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/ui_editor_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/game_bridge_spec.spl
SIMPLE_LIB=src bin/simple test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
bin/simple spipe-docgen test/01_unit/app/office/game_bridge_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The layout guard must print `0`. Generated manuals live under `doc/06_spec`;
executable specs stay under `test/`.
