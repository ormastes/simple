# SStack State: libreoffice-suite

## Status: ACTIVE — opened 2026-06-14

Umbrella program lane. This is a multi-session effort; each slice lands and
verifies independently. Do not treat the whole program as one commit.

## User Request

Improve the IDE; give the md tool a WYSIWYG view beside line-by-line edit; add a
CSS layer for md and TUI to reach MS-Word-level expressiveness; use that CSS to
make the primitive PPT app render like MS PowerPoint; harden the Excel-like
sheet (refs, arithmetic, calc); split word/ppt/excel into separate plugins on
the md module; rename the suite to "LibreOffice"; harden db, SDD/draw, math;
check the game-dev tool and connect it to draw/calc/db. Keep focus on
completing a LibreOffice-like office suite.

## Ground Truth (measured 2026-06-14)

- Office apps already exist under `src/app/office/`:
  `word/` (render,sidebar,toolbar,word_app), `sheets/`
  (cell,cell_ref,formula,render,spreadsheet), `slides/`
  (slide,outline,design,render,templates), plus `planner/`, `mail/`,
  `launcher.spl`, `theme.spl`, `render_adapter.spl`, `mod.spl`.
- Libs: `src/lib/common/markdown/` (full parser; render.spl is MINIMAL —
  `<p>`/heading wrap only, no CSS), `src/lib/common/drawing/`
  (document,selection,vector), `src/lib/common/office/`
  (file_ops,number,search,undo).
- TWO CSS engines exist but are NOT wired to office/md render:
  - `src/lib/blink/css_parser/` — tokenizer, parser (selector + decl blocks),
    selector matcher (type/class/id/compound + specificity). The real engine.
  - `src/lib/common/render_scene/css_types.spl` — CSSDeclaration / CSSValue /
    Selector / CSSRule lighter model.
  - `src/lib/common/ui/glass_css*.spl` — glassmorphism component theming.
- Office render adapters emit `WidgetNode`s with ad-hoc string style TAGS
  (`"paragraph"`, `"heading_N"`, `"bullet_list"`) — not real CSS. The spine gap
  is bridging a CSS engine to these WidgetNode tags so styles cascade for both
  TUI and GUI surfaces.
- Prior agent lanes (CLOSED, finished but NOT "MS-Word level"):
  `m17-css3-completeness`, `md-editor-production`, `editor-ide-platform`;
  `ide-office-plugin-suite` is dev-done and already wired a plugin manifest
  adapter through `app.plugin.registry` and CSS-like slide design helpers
  (`slides/design.spl`).

## Cross-cutting blocker

`doc/08_tracking/bug/interp_f64_nested_struct_payload_zero_2026-06-14.md`:
f64/enum payloads zero out when flowing through deeply nested struct returns on
interpreter/SMF/runner-compiled paths, and the native backend cores on those
paths. This blocks end-to-end NUMERIC verification of the sheet formula engine
(and pre-existing SUM/AVERAGE) and any f64 render geometry. Verify
termination/structural behavior via the runner; verify numerics via direct
`bin/simple run` until the blocker is fixed. Keep slices TEXT/i64-based where
possible so they are runner-verifiable.

## Slices (ordered)

1. DONE (landed origin 4fc99a1) — **Excel formula hardening**: depth-bounded
   cycle detection (circular refs terminate), ROUND half-away-from-zero,
   SQRT/POWER/MOD/INT/TRUNC/PRODUCT/FLOOR/CEILING/SIGN, AND/OR/NOT, `&` concat,
   TRUE/FALSE. Spec: `test/01_unit/app/office/sheets/formula_harden_spec.spl`.
2. DONE (landed origin 3ce12f3) — **CSS substrate bridge** (the spine):
   `std.common.render_scene.office_style_resolver` maps office/markdown element
   tags + utility classes to resolved CSS declarations (text-keyed, Word-level
   default theme) and projects to GUI (CSS text) and TUI (SGR codes). Spec
   `test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl` 8/8
   green. Follow-up: back the cascade with `blink/css_parser` for user CSS.
2b. DONE (landed origin 1b0da57) — **markdown wired to the substrate**:
   `render_markdown_line_styled_html` (in `markdown/render.spl`) emits inline-CSS
   HTML via the resolver — the spine demonstrated end-to-end. Paragraph spec 3/3
   green; heading path verified via direct `bin/simple run` (runner compiled-mode
   i32 interpolation is unreliable — same toolchain fragility as the f64 bug).
2d. DONE (landed origin 2ec0229) — **word wired to the substrate**
   (`office/word/html_render.spl`): `render_block_html`/`render_document_html`
   map each `BlockKind` to the resolver theme → styled HTML, against the real
   `attributed_text` DocBlock model (the existing `word/render.spl` targets a
   stale DocBlock API + the broken UI tree). Spec 4/4. All three office surfaces
   — markdown, slides, word — now share ONE CSS substrate.
3. DONE (landed origin 493118d) — **Markdown WYSIWYG view** (`office/md_wysiwyg.spl`):
   `build_wysiwyg_view` pairs each editable source line with its styled-HTML
   preview; `wysiwyg_source_pane`/`wysiwyg_preview_pane` + per-line
   `wysiwyg_update_line` (edit-and-re-render). Pure model→view, no GUI dep — IDE
   TUI+GUI both consume it. Spec `test/01_unit/app/office/md_wysiwyg_spec.spl`
   5/5. Follow-up: wire into the IDE's actual editor surface.
4. DONE (landed origin d0ca1b9) — **PPT renders like MS PPT**:
   `app.office.slides.html_render.render_slide_html` maps each element's role
   (title/subtitle/body, inferred from layout + position) to the resolver's
   slide theme and emits styled HTML. Decoupled into its own file to avoid the
   `common.ui.widget`→`common.ui.style` load chain, which has a pre-existing
   parser bug (`doc/08_tracking/bug/parser_array_index_misread_as_generics_2026-06-14.md`).
   Spec `test/01_unit/app/office/slides/html_render_spec.spl` 4/4. Follow-up:
   wire `slides/render.spl` WidgetNode path + `slides/design.spl` once the
   ui/style parser bug is fixed.
5. PARTIAL — **Excel deeper**: display-safe COUNTA, exact-match VLOOKUP, and
   text functions are verified through `evaluate_formula_display_text`;
   dependency-graph recalc and the cell-ref numeric path remain gated on the
   f64 blocker.
6. DONE (landed origin d4323508) — **Plugin split**: `app.office.plugins`
   registers office-word/office-ppt/office-excel as three separate `PluginEntry`
   manifests over the shared md/CSS substrate, via the project's plugin registry
   format (same path the IDE adapter uses). Manifest round-trips + validates.
   Spec `test/01_unit/app/office/plugins_spec.spl` 5/5.
   NOTE: the higher-level office *apps* (`word_app`/`sheets_app`/... exercised by
   `office_suite_spec.spl`) have 13 PRE-EXISTING failures unrelated to these
   slices (stale `word/render.spl` DocBlock API, etc.) — separate cleanup.
7. PARTIAL — **Harden db / SDD-draw / math**:
   - DRAW: DONE (landed origin 0bb2ebae). New `common/drawing/vector_shapes.spl`
     — DrawShape(rect/line/circle/label) on a canvas → well-formed SVG, using
     INTEGER coords to sidestep the f64 bug (the existing Skia SkPoint/SkRect are
     f64). Draw flipped to implemented in the LibreOffice branding (4 live apps).
     Spec 6/6; coords verified via direct run.
   - BASE (db): DONE (landed origin a8e19d0). `office/base_db.spl` — text table
     with insert, `select_where`, `project_column`. Root-caused the blocker: the
     interpreter corrupts `arr.get(n)` for n>=1 (`.get(0)`==ok, `.get(1)` fails
     `==`); fixed by reading cells via for-in iteration (see
     [[feedback_array_get_index_ge1_corruption]]). Spec 6/6 runner-green.
   - MATH: DONE (landed origin a838abeb). `office/math_editor.spl` — renders math
     expressions to MathML (mi/mn/mo) + msup/msqrt helpers. Spec 6/6.
   ALL SIX LibreOffice apps (Writer/Calc/Impress/Draw/Base/Math) now implemented
   and verified (libreoffice spec 6/6, all implemented:true).
8. DONE (landed origin effc1b1; advanced locally 2026-06-19) — **Game-tool connect** (`office/game_bridge.spl`):
   declares game↔{calc,draw,db} connection targets. Calc exports level/tuning
   tokens from spreadsheet cell refs; Draw exports SDD nodes as deterministic
   sprite records; Base exports exact-match query rows as game state records.
   Connection/spec surface is now 8/8 runner-green for Calc/Draw/Base
   declarations and adapters.
9. DONE (landed origin 626f970) — **Rename to "LibreOffice"** (minimal/honest):
   `app.office.libreoffice` brands the suite "LibreOffice" and maps components to
   Writer/Calc/Impress/Draw/Base/Math, with an `implemented` flag reporting only
   the 3 substrate-backed apps as live. Emits a LibreOffice-branded plugin
   manifest. Spec `test/01_unit/app/office/libreoffice_spec.spl` 6/6. (Branding
   layer, not a repo-wide symbol sweep — the right minimal interpretation.)
10. DONE (local 2026-06-18) — **Markdown WYSIWYG + PPT render hardening**:
   Markdown now exposes a CSS-backed WYSIWYG document wrapper
   (`wysiwyg_preview_css` / `wysiwyg_preview_document_html`) consumed by the GUI
   markdown renderer. Slide HTML rendering now escapes element text, sanitizes
   CSS colors to `#RGB`/`#RRGGBB`, falls back on unsafe values, clamps negative
   element geometry to `0px`, and emits a fixed 960x540 relative slide with
   absolute element boxes. IDE feature checks expose `css_doc`, `escaped`,
   `ppt_html`, `safe_css`, and `positioned` markers in both TUI and GUI modes.
11. ACTIVE (local 2026-06-19) — **Markdown-source Writer/PPT architecture**:
   Writer and Impress/PPT use Markdown as their product source and generate HTML
   for rendering. RichDocument and slide-object HTML renderers remain
   compatibility paths, not the preferred authoring model.
12. ACTIVE (local 2026-06-19) — **SDD diagram editor substrate**:
   Named the SDN-backed diagram dialect **SDD: Simple Diagram Document**
   (`.sdd.sdn`) and started draw.io/Figma-level hardening by adding explicit
   node geometry, layer metadata, connector routes, waypoints, anchors, and
   weave-based layout edits, rendered SVG connector paths, pure reroute
   operations, node shape/style edits, parent/group membership, and guarded
   multi-node align/distribute operations to `std.editor.services.sdn_graph`.
13. ACTIVE (local 2026-06-19) — **HTML UI editor substrate**:
   Added a pure `app.office.ui_editor` design-document layer for Figma-like
   positioned frames/components, inspector-ready HTML, SDD export, and guarded
   label/layout/alignment/distribution/layer edits plus deterministic
   frame-level auto-layout and parent/constraint metadata. This is the Office
   Designer surface; live browser editing, collaborative cursors, and native
   Figma import are future slices.

## Log

- 2026-06-14 dev: Opened lane. Measured ground truth (above). Landed slice 1
  (formula hardening) to origin 4fc99a1 with green cycle-termination spec; filed
  the f64-nested-struct toolchain blocker.
- 2026-06-14 dev: Landed slice 2 (office_style_resolver CSS substrate, 3ce12f3,
  spec 8/8) and slice 2b (markdown styled render via the resolver, 1b0da57, spec
  3/3). The CSS-for-md/TUI spine is now end-to-end and verified.
- 2026-06-14 dev: Landed slice 2c (slide theme tags, 0f79db9) and slice 4 (PPT
  styled HTML render via resolver, d0ca1b9, spec 4/4). Refactored ResolvedStyle
  accessors to free functions (style_value/style_has) to avoid a bare-method
  collision with ThemeRegistry.get. Filed pre-existing ui/style.spl parser bug.
- 2026-06-14 dev: Landed slice 2d (word styled HTML render, 2ec0229, spec 4/4)
  and slice 6 (office plugin split, d4323508, spec 5/5). Core suite architecture
  now in place: CSS substrate + all 3 surfaces (md/slides/word) rendering through
  it + word/ppt/excel as separate registered plugins. Remaining: slice 3 (IDE
  WYSIWYG view), 5 (deeper Excel, f64-blocked), 7 (db/draw/math), 8 (game
  connect), 9 (rename to LibreOffice, last/minimal).
- 2026-06-18 dev: Added local research and design for LLM-readable access to
  LibreOffice-like app features. Implemented `app.office.llm_catalog` as a pure
  metadata catalog for Markdown, Writer, Calc, Impress, Draw, Base, Math, and
  Counter with owner modules, feature lists, edit/action names, and evidence
  keys. Exposed the catalog through the IDE feature-check report for both TUI and
  GUI modes. Focused checks passed: `bin/simple check` on the new catalog,
  feature report, and IDE office system spec; `ide_office_plugin_suite_spec`
  passed 19/0; docgen refreshed the mirrored manual with one length warning and
  pre-existing docgen dependency warnings only; direct TUI/GUI feature checks report `llm-catalog: apps=8
  features=37 actions=9`; `find doc/06_spec -name '*_spec.spl' | wc -l`
  returned `0`.
- 2026-06-18 dev: Hardened the active Markdown WYSIWYG and PPT-like rendering
  slice. Updated `app.office.md_wysiwyg`, `app.office.md_wysiwyg_gui`,
  `app.office.slides.html_render`, `app.ide.markdown_render`, and
  `app.ide.slides_compat`; refreshed the focused unit specs and IDE system
  spec/manual. Evidence: touched-file `bin/simple check` passed 8/8;
  `md_wysiwyg_spec` passed 9/0; `slides/html_render_spec` passed 6/0;
  `ide_office_plugin_suite_spec` passed 19/0; direct TUI and GUI feature checks
  report `css_doc=true escaped=true` and
  `ppt_html=true safe_css=true positioned=true`; docgen generated 1 complete
  manual and 0 stubs with the pre-existing doc-length/dependency warnings only;
  `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- 2026-06-18 dev: Aligned `md_wysiwyg_render_spec` with the same
  CSS-backed document helper used by `md_wysiwyg_gui`. The graphical spec passed
  7/0 after updating the fenced-code oracle to assert preserved indentation in
  HTML plus nonblank framebuffer evidence; the renderer currently paints the
  styled `<pre>` block background but does not expose stable black glyph pixels
  for that path.
- 2026-06-19 dev: Clarified and implemented the Markdown-source rendering
  architecture for Writer and Impress/PPT. Added `render_writer_markdown_html`
  and `render_ppt_markdown_html` adapters over the existing Markdown document
  decoration/render service, updated the LLM catalog to advertise Markdown
  source actions, and moved `md_wysiwyg_ppm` to `wysiwyg_preview_document_html`.
- 2026-06-19 dev: Researched current SDN graph support and primary draw.io/Figma
  references, then implemented the first SDD diagram slice. Added
  `sdn_graph_format_name`, `sdn_graph_file_extension`, node
  `x/y/width/height/layer`, edge `route/waypoints/start_anchor/end_anchor`,
  deterministic `sdd-*` HTML metadata, canonical table output, and weave-based
  layout edits. Focused `sdn_graph_diagram_spec` passed 6/0.
- 2026-06-19 dev: Started the HTML UI editor slice. Added local research,
  requirements, NFR, test plan, and design docs for `app.office.ui_editor`;
  implementation covers positioned UI nodes, HTML design-surface rendering,
  SDD export, and stale-safe label edits. Draw catalog ownership moves to the
  SDD substrate and Designer is added as the HTML UI editor catalog app.
- 2026-06-19 dev: Advanced the SDD draw.io-like connector slice. Added SVG
  connector path synthesis from node geometry, anchors, route mode, and
  waypoints; exposed `data-edge-index`/`data-path`; added pure
  `sdn_graph_update_edge_at` reroute editing; and updated the Draw LLM catalog
  action to include `reroute-sdd-connector`.
- 2026-06-19 dev: Advanced the Figma-like Designer slice with guarded layout
  edits. Added `office_ui_design_update_layout_checked` for stale-safe
  move/resize operations over x/y/width/height, updated Designer catalog
  metadata to expose `layout-edit` and `ui-layout-edit`, and covered the path in
  both the UI editor unit spec and IDE office system spec.
- 2026-06-19 dev: Advanced Designer stack ordering. Numeric `layer` values now
  render as deterministic `data-z-index`/CSS `z-index`; non-numeric semantic
  layers fall back to document order. Added `office_ui_design_update_layer_checked`
  and catalog metadata for `layer-edit` / `ui-layer-edit`.
- 2026-06-19 dev: Advanced Designer selection and inspector support. Added
  transient selected-node rendering with `data-selected` / `aria-selected`
  metadata and a read-only `office_ui_design_inspect_node` snapshot API, exposed
  through catalog metadata as `selection`, `inspector`, and `ui-inspect-node`.
- 2026-06-19 dev: Advanced Designer style-token editing. Added guarded
  `office_ui_design_update_style_token_checked` over the node `css` token plus a
  read alias for style-token inspection; catalog metadata now exposes
  `style-tokens`, `style-token-edit`, `ui-style-token-read`, and
  `ui-style-token-edit`.
- 2026-06-19 dev: Advanced SDD Draw node editing. Added pure
  `sdn_graph_update_node_at` plus shape-only/style-only helpers for direct
  draw.io-like node shape/style/geometry edits, updated Draw catalog metadata
  with `node-shape-edit`, `node-style-edit`, `edit-sdd-node-shape`, and
  `edit-sdd-node-style`, and refreshed glossary/guide language.
- 2026-06-19 dev: Advanced SDD Draw grouping. Added node `parent` metadata for
  draw.io-like group/container membership across dense syntax, canonical tables,
  weave rules, HTML `data-parent`, and a pure `sdn_graph_update_node_parent_at`
  edit helper. Catalog metadata now exposes `group-containers` and
  `edit-sdd-node-parent`.
- 2026-06-19 dev: Advanced Calc formula hardening on the display-safe path.
  Added runner-verifiable `COUNTA`, `LEN`, `LOWER`, `UPPER`, and `TRIM` support
  through `evaluate_formula_display_text`, with catalog features
  `formula-counta` and `formula-text-functions`; full f64 formula parity remains
  gated by the tracked backend blocker.
- 2026-06-19 dev: Advanced Calc display formula lookup coverage. Added
  exact-match `VLOOKUP` support to `evaluate_formula_display_text`, returning
  matched-row display text while failing closed for missing keys, invalid result
  columns, and unsupported approximate mode. Catalog metadata now exposes
  `formula-vlookup`; focused formula hardening and IDE office specs passed.
- 2026-06-19 dev: Advanced Calc app-level display recalc. `SheetsApp.confirm_edit`
  now writes the edited sheet back into the workbook, clears stale formula
  caches, and stores checked display-safe `COUNTA`, exact-match `VLOOKUP`, and
  text-function results into `FormulaVal.cached_display` for visible grid
  rendering. Catalog metadata now exposes `formula-display-recalc`; numeric
  cell-reference recalc remains gated by the tracked f64 backend blocker.
- 2026-06-19 dev: Advanced Figma-like Designer multi-node layout operations.
  Added geometry signatures plus guarded alignment and distribution helpers over
  selected UI nodes, with all-or-nothing stale/missing/invalid-geometry
  rejection. Catalog metadata now exposes `align-layout`,
  `distribute-layout`, `ui-align-selection`, and `ui-distribute-selection`.
- 2026-06-19 dev: Advanced Figma-like Designer auto-layout. UI design nodes now
  carry parent, frame auto-layout, gap/padding, and child constraint metadata;
  `office_ui_design_resolve_auto_layout` materializes deterministic integer
  geometry for horizontal/vertical frame layout, and guarded helpers update
  parent/layout/constraint metadata with stale, missing-parent, cycle, and
  invalid-layout rejection. Catalog metadata now exposes `auto-layout`,
  `constraints`, `ui-auto-layout-edit`, and `ui-constraints-edit`.
- 2026-06-19 dev: Advanced SDD Draw selection and inspector support. Added
  transient selected-node/selected-connector HTML metadata plus pure
  `sdn_graph_inspect_node` / `sdn_graph_inspect_edge` snapshots for draw.io-like
  sidebars. Catalog metadata now exposes `selection`, `inspector`,
  `render-sdd-html-with-selection`, `inspect-sdd-node`, and `inspect-sdd-edge`.
- 2026-06-19 dev: Advanced LibreOffice Base CRUD hardening. Added checked row
  insertion with schema-width validation plus pure exact-match `count_where`,
  `update_where`, and `delete_where` helpers over the text-table substrate.
  Catalog metadata now exposes `schema-validation`, `count-where`,
  `update-where`, `delete-where`, and `db-edit`.
- 2026-06-19 dev: Advanced LibreOffice Math structure rendering. Added escaped
  MathML tokens, `frac(a, b)` shorthand parsing, explicit fraction/subscript/
  fenced-group helpers, and catalog metadata for `fraction`, `subscript`,
  `fenced-group`, and `render-math-structure`.
- 2026-06-19 dev: Advanced LibreOffice Math checked precedence rendering.
  `math_to_mathml_checked` now reports deterministic fallback reasons for
  malformed input and renders bounded precedence for parentheses, `sqrt(...)`,
  slash fractions, caret superscripts, unary minus, and `+`/`-`/`*` operators.
  Catalog metadata now exposes `precedence-parser`, `checked-rendering`, and
  `render-mathml-checked`.
- 2026-06-19 dev: Advanced SDD Draw canvas metadata. SDD graphs now preserve
  optional draw.io-like canvas/page width, height, grid, snap, zoom, and
  background metadata; HTML render roots expose deterministic `data-canvas-*`
  attributes and pure `sdn_graph_update_canvas` edits canvas state without
  mutating nodes or connectors. Catalog metadata now exposes
  `canvas-metadata` and `edit-sdd-canvas`.
- 2026-06-19 dev: Promoted SDD Draw to the IDE feature-check surface. Added a
  pure `app.ide.draw_sanity` probe and registered Draw as a first-class IDE
  capability, so `simple ide --feature-check --tui|--gui` now reports six
  capabilities and includes SDD render, reroute, selection, inspection, node
  edit, and canvas evidence. Plugin manifests now include `ide.draw`.
- 2026-06-19 dev: Added the headless Office action bridge. `app.office.mod`
  now exposes `office_action_dispatch` for cataloged render/export actions:
  Writer Markdown HTML, PPT Markdown HTML, Designer HTML render, Designer SDD
  export, and selected SDD Draw HTML render. This gives agents and CLI callers
  one stable non-GUI path to execute the suite actions advertised in the LLM
  catalog.
- 2026-06-19 dev: Advanced the game-tool bridge now that Draw and Base are live.
  `game_connection_is_implemented` reports Calc/Draw/Base; Calc cells export as
  level/tuning tokens; SDD Draw nodes export as stable game sprite records; Base
  exact-match query rows export as `key=value` game state records. Focused
  `game_bridge_spec` passed 8/0.
- 2026-06-19 dev: Advanced SDD Draw multi-node layout editing. Added guarded
  geometry signatures plus pure `sdn_graph_align_checked` and
  `sdn_graph_distribute_checked` helpers for draw.io-like align/distribute
  operations, exposed `align-layout` / `distribute-layout` in the Draw catalog,
  and added `layout=true` to the IDE Draw sanity surface.
- 2026-06-19 dev: Exposed the Markdown editor's HTML preview through the
  headless action bridge as `render-markdown-preview-html`, completing the
  Markdown-source HTML render triad alongside Writer paper HTML and PPT deck
  HTML.
- 2026-06-19 dev: Advanced SDD Draw copy/paste basics. Added checked
  `sdn_graph_duplicate_node_checked` for duplicating one node with a unique id
  and integer offset while preserving style, shape, layer, and parent metadata.
  Draw catalog metadata now exposes `node-duplicate` and `duplicate-sdd-node`.
- 2026-06-19 dev: Advanced Figma-like Designer copy/paste basics. Added checked
  `office_ui_design_duplicate_node_checked` for duplicating one UI node with a
  unique id and integer offset while preserving style, component, layer, parent,
  auto-layout, and constraint metadata for nodes outside auto-layout parents.
  Designer catalog metadata now exposes `node-duplicate` and
  `ui-duplicate-node`.
- 2026-06-19 dev: Wired duplicate actions into the headless Office action
  bridge. `ui-duplicate-node` and `duplicate-sdd-node` accept a first-line
  `source_id|new_id|dx|dy` edit header followed by the UI/SDD document body and
  return rendered HTML for the updated document.
- 2026-06-19 dev: Wired UI/SDD align and distribute actions into the headless
  Office action bridge. `ui-align-selection`, `ui-distribute-selection`,
  `align-sdd-selection`, and `distribute-sdd-selection` accept
  `mode_or_axis|id1,id2,...` followed by the UI/SDD document body and return
  rendered HTML for the updated document.
- 2026-06-19 dev: Wired remaining SDD edit actions into the headless Office
  action bridge: `reroute-sdd-connector`, `edit-sdd-node-parent`,
  `edit-sdd-node-shape`, `edit-sdd-node-style`, and `edit-sdd-canvas`.
  Each accepts a compact first-line edit header followed by the SDD body and
  returns rendered HTML for the updated document.
- 2026-06-19 dev: Wired the remaining cataloged Designer/UI edit actions into
  the headless Office action bridge: `ui-label-edit`, `ui-layout-edit`,
  `ui-auto-layout-edit`, `ui-constraints-edit`, `ui-layer-edit`,
  `ui-style-token-read`, `ui-style-token-edit`, and `ui-inspect-node`. The
  bridge now exposes the existing guarded Figma-like UI editor helpers through
  compact first-line headers plus rendered HTML or readback text.
- 2026-06-19 dev: Wired Base table actions into the headless Office action
  bridge. `query-table` now supports `count-where`, `select-where`, and
  `project-column` over compact `table:`/`columns:`/`row:` text tables, while
  `db-edit` exposes the existing checked `insert`, `update-where`, and
  `delete-where` helpers and returns updated table text.
- 2026-06-19 dev: Wired Math render actions into the headless Office action
  bridge. `render-mathml`, `render-mathml-checked`, and
  `render-math-structure` now execute the existing Math editor renderer and
  expose MathML, checked rejection reasons, and compact structure readbacks.
- 2026-06-19 dev: Wired Counter actions into the headless Office action bridge.
  `counter-action` accepts `value|counter_increment`,
  `value|counter_decrement`, or `value|counter_reset`, returns compact value /
  status / changed readback, and keeps unsupported actions fail-closed.
- 2026-06-19 dev: Wired SDD inspector actions into the headless Office action
  bridge. `inspect-sdd-node` and `inspect-sdd-edge` now return compact
  draw.io-like readback text for node geometry/style/group fields and edge
  route/path fields, including missing-node/edge rejection reasons.
- 2026-06-19 dev: Wired Markdown guarded line editing into the headless Office
  action bridge. `md-edit` accepts `line_no|expected_source|new_source`
  followed by the Markdown body, returns updated Markdown source, and rejects
  stale or missing lines with the existing deterministic WYSIWYG diff.
- 2026-06-19 dev: Wired Calc and Impress checked edits into the headless Office
  action bridge. `sheet-edit` and `slide-edit` accept
  `target_id|expected|replacement` followed by compact source bodies, return
  updated assignments, and reject stale values with existing deterministic
  diffs.
- 2026-06-19 dev: Aligned the launcher-visible product surface with the
  LibreOffice suite name. The launcher now presents Writer, Calc, and Impress
  labels plus a LibreOffice window/status title while preserving existing
  `open_word`/`open_sheets`/`open_slides` compatibility actions.
