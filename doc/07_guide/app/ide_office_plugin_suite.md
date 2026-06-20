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
LibreOffice app names Writer, Calc, Impress, Draw, Base, and Math while
compatible actions remain `open_word`, `open_sheets`, `open_slides`,
`open_draw`, `open_db`, and `open_math`. `run_office` accepts those launcher
action names and normalizes them to the same app routes. It also accepts direct
LibreOffice/file-format aliases: `calc`/`excel`, `impress`/`ppt`, and
`base`/`db`. IDE launch feature checks report both Office launcher action and
card counts so launcher metadata cannot drift from the product surface.
The CLI `word` and `writer` routes load the Markdown-backed Writer surface; the
older rich-text `WordApp` remains only as a compatibility UI module.

## Glossary

- Writer: Markdown-backed document editor; aliases `writer`, `word`, `markdown`, `md`.
- Calc: spreadsheet editor; aliases `calc`, `sheets`, `excel`, `ods`, `xlsx`.
- Impress: Markdown-backed slide editor; aliases `impress`, `slides`, `ppt`, `odp`, `pptx`.
- Draw: SDD Diagram Draw over the SDN graph substrate; aliases `draw`, `diagram`, `sdd`, `sdn`.
  Selected connector handles expose edit actions, stable handle indexes,
  endpoint/opposite-node ids, anchors, and coordinates for Draw-style reconnect,
  label, and waypoint editing.
- Base: text-table database editor; aliases `base`, `db`, `database`.
- Math: MathML formula editor; aliases `math`, `formula`, `mathml`.
- Designer: HTML UI design editor; aliases `designer`, `ui`, `html-ui`, `figma`.
- SDD: Simple Diagram Document, the Office Draw file model stored as SDN text.
- SDN: Simple Data Notation, the table-oriented substrate used by SDD and Simple docs.

Markdown GUI rendering must use `wysiwyg_preview_document_html`, not a bare
preview pane. The document helper owns the stable `.wysiwyg-preview` CSS wrapper
and line-addressable `.wysiwyg-preview-line` rows for the escaped styled HTML
generated from source lines. Shared Markdown inline HTML helpers escape ordinary
text and marker interiors before returning `<code>`, `<strong>`, `<em>`,
`<del>`, or `<a>` fragments.
Markdown task-list lines (`- [x]` / `- [ ]`) render as escaped disabled
checkbox rows inside the same WYSIWYG document wrapper. Markdown bullet and
ordered list lines render as HTML lists, and blockquote lines render as quote
blocks with escaped inline content. Fenced code blocks render as escaped
`<pre><code>` content.

Writer rendering must expose Markdown source -> paper/document HTML through
`render_writer_markdown_html`, with root metadata for format and source line
count. Writer paper HTML renders Markdown headings, paragraphs, fenced code,
thematic breaks, blockquotes, task lists, ordered and unordered lists, tables, images, and inline links as
document HTML with body-relative `data-source-line` block anchors while escaping user text and attributes. Unsafe Markdown image and
stylesheet URLs render as `#`; Markdown table separator
alignment markers (`:---`, `---:`, `:-:`) become stable `data-align` and
`text-align` cell metadata, and table cells expose `data-row-index` /
`data-column-index` coordinates for selection and range-copy tooling. The rich-text compatibility adapter must also escape
block text before emitting HTML.

PPT/Impress rendering must expose Markdown source -> slide-deck HTML through
`render_ppt_markdown_html`, with root metadata for format and slide count. The
object-model slide renderer remains a
compatibility path and should escape element text, sanitize CSS colors to simple
`#RGB` or `#RRGGBB` values, drop unsafe Markdown slide class tokens, clamp negative geometry to `0px`, and emit a fixed
960x540 relative slide with stable slide/element metadata, Markdown body
`data-source-line` slide anchors, and absolutely
positioned element boxes.

Headless Office actions are exposed through
`office_action_dispatch(action, source)` in `app.office.mod`. This is the stable
non-GUI bridge for cataloged render/export actions:
`render-markdown-preview-html`, `render-writer-markdown-html`,
`render-ppt-markdown-html`, `render-ui-html`,
`render-ui-html-with-selection`, `export-ui-sdd`, and
`render-sdd-html-with-selection`. The bridge delegates to the canonical
Markdown, Writer, Impress, Designer, and SDD renderers rather than
duplicating rendering logic. Legacy aliases `ui-render`, `ui-export-sdd`, and
`render-sdd` normalize to those canonical action names.
`render-ui-html-with-selection` accepts either raw UI design source or a
first-line `select|node_id` header followed by UI design source.
`render-sdd-html-with-selection` accepts either raw SDD source or a first-line
`select|node_id|edge_index` header followed by SDD source; leave `edge_index`
blank to select only a node.

`render-markdown-preview-html` exposes the Markdown editor's own
`wysiwyg_preview_document_html` route through the same headless bridge, so the
suite has a triad of Markdown-source HTML render actions: Markdown preview,
Writer paper HTML, and PPT deck HTML.
`md-edit` accepts `line_no|expected_source|new_source` followed by the Markdown
body and returns updated Markdown source, rejecting stale lines with a
deterministic diff.

Duplicate actions use a compact first-line edit header:
`source_id|new_id|dx|dy`, followed by the UI or SDD document body. The
`ui-duplicate-node` action returns rendered UI HTML and rejects malformed new
node IDs as `invalid-args`; `duplicate-sdd-node` returns rendered SDD HTML and
rejects malformed source or new node IDs as `invalid-args`.
Blank duplicate source/new IDs or offsets are rejected as `invalid-args`.

Designer edit actions use compact first-line edit headers followed by the UI
design body. `ui-label-edit` uses `node_id|expected_label|new_label`.
`ui-name-edit` uses `expected_name|new_name`; the new name is required.
`ui-canvas-edit` uses `expected_width|expected_height|new_width|new_height`;
all fields are required non-negative integers.
`ui-layout-edit` and `ui-resize-node` use `node_id|expected_x|expected_y|expected_width|expected_height|new_x|new_y|new_width|new_height`; x/y fields are signed integers and width/height fields are non-negative integers.
`ui-auto-layout-edit` uses `node_id|expected_mode|expected_gap|expected_padding|new_mode|new_gap|new_padding`; all compact header fields are required, and malformed replacement mode, gap, or padding fields are `invalid-args`.
`ui-constraints-edit` uses `node_id|expected_h|expected_v|new_h|new_v`; all compact header fields are required, and malformed replacement constraint fields are `invalid-args`.
Blank or malformed `ui-label-edit`, `ui-layout-edit`, `ui-resize-node`,
`ui-auto-layout-edit`, and `ui-constraints-edit` / `ui-layer-edit` /
`ui-style-token-edit` node ids are rejected as `invalid-args`.
`ui-kind-edit`, `ui-layer-edit`, `ui-component-edit`, and `ui-style-token-edit`
use `node_id|expected|new`; blank expected kind/layer/style fields and blank or
malformed replacement kind/style-token fields are `invalid-args`.
`ui-component-edit` accepts a blank replacement to clear component metadata, or
a safe token to set it.
`ui-style-token-read` and `ui-inspect-node` use `node_id`, reject malformed IDs
as `invalid-args`, and return compact readback text.

Layout actions use `mode_or_axis|id1,id2,...`, followed by the UI or SDD
document body. `ui-align-selection`, `ui-distribute-selection`,
`align-sdd-selection`, and `distribute-sdd-selection` compute the current
geometry signature and return rendered HTML for the updated document.
Blank or malformed layout modes/axes, blank selection lists, or malformed
selection IDs are rejected as `invalid-args`.

SDD node edit actions use `node_id|value` for label, parent, shape, style, layer, and role edits; style labels are space-separated safe tokens, and shape, layer, and role are empty or one safe token.
Blank or malformed SDD node edit ids are rejected as `invalid-args`.
Parent edits reject malformed replacement parent IDs, missing parent IDs, and parent cycles.
`add-sdd-node` uses `id|label|css|role|shape|x|y|width|height|layer|parent`
and rejects duplicate IDs, blank IDs, missing parent IDs, malformed geometry, and unsafe style, role, shape, or layer tokens.
`order-sdd-node` uses `node_id|front` or `node_id|back` to change document/render order.
Blank or malformed SDD order node ids are rejected as `invalid-args`.
`edit-sdd-style-rule` uses `css|target|extends|key|value` and returns canonical SDD text; `css`, `target`, and `key` are required, and `extends` must be `none`, empty, or an existing non-self CSS rule.
`delete-sdd-style-rule` uses `css|key`, rejects malformed css/key tokens as `invalid-args`, and returns canonical SDD text with that reusable rule removed.
`inspect-sdd-style-rule` uses `css|key`, rejects malformed css/key tokens as `invalid-args`, and returns compact style-rule readback text.
Blank SDD style-rule css or key arguments are rejected as `invalid-args`.
`edit-sdd-node-geometry` uses `node_id|x|y|width|height`; `x` and `y` are signed integers, and size fields are non-negative integers.
Blank or malformed SDD geometry node ids are rejected as `invalid-args`.
`delete-sdd-node` uses `node_id`, rejects blank or malformed IDs, and removes attached connectors.
`edit-sdd-canvas` uses `width|height|grid|snap|zoom|background`; every field is required, numeric fields must be non-negative integers, snap is `true` or `false`, and background must be a safe CSS value.
`add-sdd-edge` uses `from_id|to_id|label|css|kind|route|waypoints|start|end` and applies the same route, anchor, waypoint, and `invalid-args` validation as connector reroute.
`duplicate-sdd-edge` uses `edge_index`.
`edit-sdd-node-label` uses `node_id|new_label` and rejects missing node IDs.
`edit-sdd-edge-label` uses `edge_index|new_label` and rejects missing edge indexes.
`edit-sdd-edge-label-point` uses `edge_index|label_x|label_y`; label coordinates are required signed integers, and blank or malformed coordinates are `invalid-args`.
`edit-sdd-edge-style` uses `edge_index|css_labels`; labels are space-separated safe tokens.
`edit-sdd-edge-kind` uses `edge_index|kind`; kind is empty or one safe token.
`edit-sdd-edge-endpoints` uses `edge_index|from_id|to_id`; endpoint IDs must exist.
Blank or malformed SDD edge endpoint IDs are rejected as `invalid-args`.
`delete-sdd-edge` uses `edge_index` and rejects missing connector indexes.
`reroute-sdd-connector` uses `edge_index|route|waypoints|start_anchor|end_anchor`; route is empty, `simple`, or `orthogonal`, anchors are empty or cardinal, waypoints use semicolon-separated integer `x` pairs, and malformed route fields are `invalid-args`.
Node, edge, canvas, layout, and connector edit actions return rendered SDD HTML
for the updated document. Style-rule edit/delete actions return canonical SDD
text for round-trip persistence.
`inspect-sdd-node` uses `node_id`; `inspect-sdd-edge` uses `edge_index`;
`inspect-sdd-style-rule` uses `css|key`. Malformed node IDs and style-rule tokens are `invalid-args`. Inspectors return compact readback
text for geometry, style, group child metadata, route, rendered path metadata,
and style-rule fields.

Base table actions use a compact text table body:
`table: Name`, `columns: id,status`, then `row: 1,open` lines. `query-table`
uses `count-where|column|value`, `select-where|column|value`, or
`project-column|column`; blank query columns are `invalid-args`, and table bodies reject blank table names plus missing, blank, duplicate, or row-width-mismatched columns.
`render-base-table-html` renders that same table body as escaped HTML with
`data-format="base-table"`, `data-column-count`, `data-row-count`,
`data-row-index`, and escaped `data-row-index`/`data-column` cell coordinates, and rejects blank
table names plus missing, blank, duplicate, or row-width-mismatched columns. `db-edit` uses `insert|v1,v2`,
`update-where|match_column|match_value|update_column|new_value`, or
`delete-where|match_column|match_value`, rejects blank edit columns as
`invalid-args`, rejects invalid schemas, and returns the updated table text.

Calc and Impress edit actions use `target_id|expected|replacement` followed by
the compact `A1=value;B1=value` or `element_id=value;...` body. `sheet-edit`
rejects blank target refs and malformed, invalid, or duplicate source cell refs.
`slide-edit` rejects blank target ids and malformed, missing, or duplicate source element ids.
`sheet-edit` and `slide-edit` return the updated target assignment and reject stale
values with deterministic diffs.

Math actions accept one expression body. `render-mathml` returns MathML,
`render-mathml-checked` returns MathML with malformed-input rejection reasons,
and `render-math-structure` returns compact structure readback markers such as
`contains=fraction`, `contains=superscript`, or `contains=square-root`.
Full MathML documents expose `data-format="mathml"` and `data-token-count` root
metadata for IDE/readback parity with the other Office renderers.

Counter actions use `value|counter_increment`, `value|counter_decrement`, or
`value|counter_reset` and return `value=...`, `status=...`, and
`changed=...`. Blank action names are `invalid-args`; unsupported named actions
fail closed and preserve the original value.

Designer/UI editing uses `app.office.ui_editor` as a pure HTML design document
substrate. It parses positioned frame/component records, renders a stable
`.office-ui-design` HTML surface with inspector and canvas metadata, exports
node/frame/component counts to the root, emits document-order `data-node-index`
and geometry `data-x`/`data-y`/`data-width`/`data-height` metadata plus
`data-child-count`/`data-has-children` hierarchy metadata for layer and inspector panels, exports nodes to SDD-compatible tables
with quoted cells for spaces, commas, and quotes, and guards label/layout/layer
edits with expected-value checks. Numeric layer values render as deterministic `data-z-index` / CSS
`z-index` values; semantic layer names fall back to document-order stack values.
Selection and inspection are read-only derived views: selected renders add
`data-selected`/`aria-selected` metadata plus deterministic
visible `data-resize-handle` corner handles tagged with stable
`data-edit-action="resize-node"`, `data-handle-index`, `data-handle-label`,
`data-anchor-x`/`data-anchor-y`, `data-opposite-anchor-x`/`data-opposite-anchor-y`,
`data-delta-x`/`data-delta-y`, `data-cursor`, `data-node`, and
`data-node-index`, and `ui-inspect-node` returns a node
snapshot without mutating the design document. Style-token reads and guarded
style-token edits expose the node `css` token as a deterministic visual class;
they do not accept arbitrary CSS blocks. Rendered Designer classes are emitted
only for safe space-separated style tokens as `office-ui-css-*`; unsafe parsed
tokens remain inspectable metadata but do not become CSS classes. Multi-node
alignment and distribution use geometry signatures as stale-selection guards and remain integer-only,
all-or-nothing edits over selected nodes. Frame-level auto-layout resolves
horizontal/vertical child placement from integer gap/padding metadata, and
parent/constraint edits materialize deterministic Figma-like child geometry
without delegating to a browser layout engine.

Draw/diagram editing should use the product-facing name `SDD Diagram Draw` and
prefer the SDD substrate in
`std.editor.services.sdn_graph` as the Office Draw file model, not a
relationship-only graph format, for geometry, layers, connector routes,
waypoints, anchors, rendered SVG connector paths, pure edge reroute operations,
parent/group metadata, transient selection rendering, pure node/edge inspector
snapshots, pure node shape/style/parent edit operations, guarded multi-node
alignment/distribution, visible selected-node resize handles, selected connector endpoint/waypoint/label handles, rendered shape CSS with safe `sdn-css-*` and `sdd-shape-*` classes, safe `sdd-kind-*` connector classes, rendered canvas/page background and grid metadata, and rendered node order/label metadata. `src/app/ide/draw_sanity.spl`
is the product feature-check bridge:
it proves render, selection, inspection, reroute, node edit, multi-node layout,
and canvas metadata without starting GUI/browser/host APIs. Legacy SVG shape helpers remain
compatibility utilities, not the LLM catalog owner for Draw.
Rendered SDD `css_file` metadata follows the same unsafe-resource policy as
Markdown stylesheet metadata: `javascript:` and `data:` values render as `#`.
The IDE capability registry must also carry non-empty `feature_check` marker text
for every capability so plugin metadata cannot silently drift from the report.
Plugin manifest and LLM catalog entries must keep non-empty libraries/modules,
evidence keys, and action/function names; duplicate app, action, or function
symbols are invalid. The Office plugin registry is derived from the LLM catalog
and registers Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, and
Counter as separate plugin entries over the shared Markdown, HTML/CSS, and SDN
substrates. Every LLM catalog action must be recognized by
`office_action_dispatch`; blank input may fail with `invalid-args`, but never
`unknown-action`. IDE manifest entries must advertise exactly
`ide_capability_<capability>` and `ide_feature_check_<capability>` symbols for
each IDE capability. The IDE plugin-manifest feature check also reports the
LibreOffice-branded plugin entry count and manifest round-trip count as
`libre=6 libre_roundtrip=6`.

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
IDE/LLM callers use `export-sdd-game-sprites` for Draw sprite manifests and
`export-base-game-state` for Base `key=value` state lines.

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

- Markdown: `task_list=true strike=true link=true list=true ordered_list=true quote=true code=true css_doc=true escaped=true metadata=true`
- Slides: `ppt_html=true safe_css=true positioned=true element_meta=true`
- Draw: `format=sdd name="SDD: Simple Diagram Document" html=true route=true select=true inspect=true child_meta=true path_meta=true handle_meta=true edit=true geometry=true layer=true order=true role=true node_create=true style_rule=true style_delete=true style_inspect=true edge_create=true edge_duplicate=true edge_label_point=true edge_style=true edge_kind=true reconnect=true delete=true node_delete=true layout=true canvas=true`
- Calc: `display_recalc=true`
- LLM catalog: Markdown has `render-markdown-preview-html` and `md-edit`; Writer has
  `render-writer-markdown-html` plus Markdown paper features for task lists,
  tables/table alignment, images, inline links, fenced code, blockquotes,
  thematic breaks, and URL sanitizing; Impress has
  `render-ppt-markdown-html` plus PPT HTML, slide-count metadata, safe CSS,
  positioned elements, element metadata, class sanitizing, and text escaping; Draw is SDD-backed with
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
  `formula-display-recalc`; Base has `schema-validation`, `html-render`,
  `html-cell-coordinates`, `html-escape`, invalid schema rejection, `query-table`,
  `count-where`, `select-where`, `project-column`, `update-where`,
  `delete-where`, `render-base-table-html`, and `db-edit`; Math has `fraction`,
  `subscript`, `fenced-group`, `precedence-parser`, `xml-escape`,
  `sqrt-shorthand`, `slash-fraction`, `malformed-fallback`, `checked-rendering`,
  `render-mathml`, `render-math-structure`, and `render-mathml-checked`;
  Counter has `counter-action`; Designer has `selected-resize-handles`,
  `resize-handle-metadata`, `render-ui-html`, `render-ui-html-with-selection`, `export-ui-sdd`, and
  `ui-label-edit` / `ui-name-edit` / `ui-kind-edit` / `ui-canvas-edit` / `ui-layout-edit` / `ui-resize-node` / `ui-auto-layout-edit` /
  `ui-resolve-auto-layout` / `ui-duplicate-node` /
  `ui-constraints-edit` / `ui-parent-edit` / `ui-align-selection` /
  `ui-distribute-selection` / `ui-layer-edit` / `ui-component-edit` /
  `ui-style-token-read` / `ui-style-token-edit` / `ui-inspect-node`; the IDE
  feature check reports `designer: resize_handle_metadata=true` from a pure
  selected-node render.
  `office_llm_action_input_schema(action)` must return a non-empty compact
  source grammar for every advertised action so agents can call Draw, Designer,
  Base, Math, Markdown, Writer, Calc, Impress, and Counter without scraping this
  guide.

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
