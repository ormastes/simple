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

The launcher-visible product name is `LibreOffice`; cards should use the
LibreOffice app names Writer, Calc, and Impress even while the legacy compatible
actions remain `open_word`, `open_sheets`, and `open_slides`.
The CLI `word` and `writer` routes load the Markdown-backed Writer surface; the
older rich-text `WordApp` remains only as a compatibility UI module.

Markdown GUI rendering must use `wysiwyg_preview_document_html`, not a bare
preview pane. The document helper owns the stable `.wysiwyg-preview` CSS wrapper
and line-addressable `.wysiwyg-preview-line` rows for the escaped styled HTML
generated from source lines.

Writer rendering must expose Markdown source -> paper/document HTML through
`render_writer_markdown_html`, with root metadata for format and source line
count.

PPT/Impress rendering must expose Markdown source -> slide-deck HTML through
`render_ppt_markdown_html`, with root metadata for format and slide count. The
object-model slide renderer remains a
compatibility path and should escape element text, sanitize CSS colors to simple
`#RGB` or `#RRGGBB` values, clamp negative geometry to `0px`, and emit a fixed
960x540 relative slide with absolutely positioned element boxes.

Headless Office actions are exposed through
`office_action_dispatch(action, source)` in `app.office.mod`. This is the stable
non-GUI bridge for cataloged render/export actions:
`render-markdown-preview-html`, `render-writer-markdown-html`,
`render-ppt-markdown-html`, `render-ui-html`, `export-ui-sdd`, and
`render-sdd-html-with-selection`. The bridge delegates to the canonical
Markdown, Writer, Impress, Designer, and SDD renderers rather than
duplicating rendering logic.

`render-markdown-preview-html` exposes the Markdown editor's own
`wysiwyg_preview_document_html` route through the same headless bridge, so the
suite has a triad of Markdown-source HTML render actions: Markdown preview,
Writer paper HTML, and PPT deck HTML.
`md-edit` accepts `line_no|expected_source|new_source` followed by the Markdown
body and returns updated Markdown source, rejecting stale lines with a
deterministic diff.

Duplicate actions use a compact first-line edit header:
`source_id|new_id|dx|dy`, followed by the UI or SDD document body. The
`ui-duplicate-node` action returns rendered UI HTML; `duplicate-sdd-node`
returns rendered SDD HTML.

Designer edit actions use compact first-line edit headers followed by the UI
design body. `ui-label-edit` uses `node_id|expected_label|new_label`.
`ui-layout-edit` uses `node_id|expected_x|expected_y|expected_width|expected_height|new_x|new_y|new_width|new_height`.
`ui-auto-layout-edit` uses `node_id|expected_mode|expected_gap|expected_padding|new_mode|new_gap|new_padding`.
`ui-constraints-edit` uses `node_id|expected_h|expected_v|new_h|new_v`;
`ui-layer-edit` and `ui-style-token-edit` use `node_id|expected|new`.
`ui-style-token-read` and `ui-inspect-node` use `node_id` and return compact
readback text.

Layout actions use `mode_or_axis|id1,id2,...`, followed by the UI or SDD
document body. `ui-align-selection`, `ui-distribute-selection`,
`align-sdd-selection`, and `distribute-sdd-selection` compute the current
geometry signature and return rendered HTML for the updated document.

SDD node edit actions use `node_id|value` for label, parent, shape, style, layer, and role edits.
`add-sdd-node` uses `id|label|css|role|shape|x|y|width|height|layer|parent`.
`order-sdd-node` uses `node_id|front` or `node_id|back` to change document/render order.
`edit-sdd-style-rule` uses `css|target|extends|key|value` and returns canonical SDD text.
`delete-sdd-style-rule` uses `css|key` and returns canonical SDD text with that reusable rule removed.
`inspect-sdd-style-rule` uses `css|key` and returns compact style-rule readback text.
`edit-sdd-node-geometry` uses `node_id|x|y|width|height`.
`delete-sdd-node` uses `node_id` and removes attached connectors.
`edit-sdd-canvas` uses `width|height|grid|snap|zoom|background`.
`add-sdd-edge` uses `from_id|to_id|label|css|kind|route|waypoints|start|end`.
`duplicate-sdd-edge` uses `edge_index`.
`edit-sdd-edge-label` uses `edge_index|new_label`.
`edit-sdd-edge-label-point` uses `edge_index|label_x|label_y`.
`edit-sdd-edge-style` uses `edge_index|css_labels`.
`edit-sdd-edge-kind` uses `edge_index|kind`.
`edit-sdd-edge-endpoints` uses `edge_index|from_id|to_id`.
`delete-sdd-edge` uses `edge_index`.
`reroute-sdd-connector` uses `edge_index|route|waypoints|start_anchor|end_anchor`.
Node, edge, canvas, layout, and connector edit actions return rendered SDD HTML
for the updated document. Style-rule edit/delete actions return canonical SDD
text for round-trip persistence.
`inspect-sdd-node` uses `node_id`; `inspect-sdd-edge` uses `edge_index`;
`inspect-sdd-style-rule` uses `css|key`. Inspectors return compact readback
text for geometry, style, route, rendered path metadata, and style-rule fields.

Base table actions use a compact text table body:
`table: Name`, `columns: id,status`, then `row: 1,open` lines. `query-table`
uses `count-where|column|value`, `select-where|column|value`, or
`project-column|column`. `render-base-table-html` renders that same table body
as escaped HTML with `data-format="base-table"`, `data-column-count`, and
`data-row-count`. `db-edit` uses `insert|v1,v2`,
`update-where|match_column|match_value|update_column|new_value`, or
`delete-where|match_column|match_value`, and returns the updated table text.

Calc and Impress edit actions use `target_id|expected|replacement` followed by
the compact `A1=value;B1=value` or `element_id=value;...` body. `sheet-edit`
and `slide-edit` return the updated target assignment and reject stale values
with deterministic diffs.

Math actions accept one expression body. `render-mathml` returns MathML,
`render-mathml-checked` returns MathML with malformed-input rejection reasons,
and `render-math-structure` returns compact structure readback markers such as
`contains=fraction`, `contains=superscript`, or `contains=square-root`.
Full MathML documents expose `data-format="mathml"` and `data-token-count` root
metadata for IDE/readback parity with the other Office renderers.

Counter actions use `value|counter_increment`, `value|counter_decrement`, or
`value|counter_reset` and return `value=...`, `status=...`, and
`changed=...`. Unsupported actions fail closed and preserve the original value.

Designer/UI editing uses `app.office.ui_editor` as a pure HTML design document
substrate. It parses positioned frame/component records, renders a stable
`.office-ui-design` HTML surface with inspector and canvas metadata, exports
nodes to SDD-compatible tables, and guards label/layout/layer edits with
expected-value checks. Numeric layer values render as deterministic `data-z-index` / CSS
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
snapshots, pure node shape/style/parent edit operations, guarded multi-node
alignment/distribution, rendered shape CSS, and rendered canvas/page background and grid metadata. `src/app/ide/draw_sanity.spl`
is the product feature-check bridge:
it proves render, selection, inspection, reroute, node edit, multi-node layout,
and canvas metadata without starting GUI/browser/host APIs. Legacy SVG shape helpers remain
compatibility utilities, not the LLM catalog owner for Draw.
The IDE capability registry must also carry non-empty `feature_check` marker text
for every capability so plugin metadata cannot silently drift from the report.
Plugin manifest entries must advertise exactly `ide_capability_<capability>` and
`ide_feature_check_<capability>` symbols for each IDE capability.

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

- Markdown: `css_doc=true escaped=true metadata=true`
- Slides: `ppt_html=true safe_css=true positioned=true`
- Draw: `html=true route=true select=true inspect=true path_meta=true edit=true geometry=true layer=true order=true role=true node_create=true style_rule=true style_delete=true style_inspect=true edge_create=true edge_duplicate=true edge_label_point=true edge_style=true edge_kind=true reconnect=true delete=true node_delete=true layout=true canvas=true`
- LLM catalog: Markdown has `render-markdown-preview-html` and `md-edit`; Writer has
  `render-writer-markdown-html`; Impress has
  `render-ppt-markdown-html`; Draw is SDD-backed with
  `render-sdd-html-with-selection`, `reroute-sdd-connector`, `edit-sdd-style-rule`,
  `delete-sdd-style-rule`, `inspect-sdd-style-rule`, `add-sdd-node`, `add-sdd-edge`,
  `duplicate-sdd-edge`, `edit-sdd-edge-label`, `edit-sdd-edge-label-point`, `edit-sdd-edge-style`, `edit-sdd-edge-kind`, `edit-sdd-edge-endpoints`,
  `delete-sdd-edge`, `delete-sdd-node`, `edit-sdd-node-geometry`,
  `edit-sdd-node-label`, `edit-sdd-node-parent`, `edit-sdd-node-shape`,
  `edit-sdd-node-style`, `edit-sdd-node-layer`, `order-sdd-node`, `edit-sdd-node-role`,
  `duplicate-sdd-node`, `edit-sdd-canvas`, `align-sdd-selection`,
  `distribute-sdd-selection`, `inspect-sdd-node`, and `inspect-sdd-edge`;
  Calc has `formula-counta`,
  `formula-text-functions`, `formula-vlookup`, and
  `formula-display-recalc`; Base has `schema-validation`, `html-render`, `query-table`,
  `count-where`, `select-where`, `project-column`, `update-where`,
  `delete-where`, `render-base-table-html`, and `db-edit`; Math has `fraction`,
  `subscript`, `fenced-group`, `precedence-parser`, `checked-rendering`,
  `render-mathml`, `render-math-structure`, and `render-mathml-checked`;
  Counter has `counter-action`; Designer has
  `render-ui-html`, `export-ui-sdd`, and
  `ui-label-edit` / `ui-layout-edit` / `ui-auto-layout-edit` /
  `ui-duplicate-node` / `ui-constraints-edit` / `ui-align-selection` /
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
  src/lib/editor/services/sdn_graph.spl \
  src/app/ide/markdown_render.spl \
  src/app/ide/slides_compat.spl \
  test/01_unit/app/office/md_wysiwyg_spec.spl \
  test/01_unit/app/office/md_wysiwyg_render_spec.spl \
  test/01_unit/app/office/slides/html_render_spec.spl \
  test/01_unit/app/office/ui_editor_spec.spl \
  test/01_unit/app/office/game_bridge_spec.spl \
  test/01_unit/editor/services/sdn_graph_diagram_spec.spl \
  test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl

SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/slides/html_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/ui_editor_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/game_bridge_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/editor/services/sdn_graph_diagram_spec.spl
SIMPLE_LIB=src bin/simple test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
bin/simple spipe-docgen test/01_unit/app/office/game_bridge_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/01_unit/editor/services/sdn_graph_diagram_spec.spl --output doc/06_spec --no-index
bin/simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The layout guard must print `0`. Generated manuals live under `doc/06_spec`;
executable specs stay under `test/`.
