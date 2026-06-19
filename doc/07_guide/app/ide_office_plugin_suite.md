# IDE Office Plugin Suite Guide

The IDE Office plugin suite exposes Markdown, slides, sheets, dashboard, DB
admin, and LibreOffice-like app catalog checks through
`src/app/ide/feature_report.spl`.

## Canonical Surfaces

- Markdown WYSIWYG model: `src/app/office/md_wysiwyg.spl`
- Markdown GUI render entry: `src/app/office/md_wysiwyg_gui.spl`
- Writer Markdown render: `src/app/office/word/html_render.spl`
- IDE Markdown probe: `src/app/ide/markdown_render.spl`
- Slide/PPT HTML render: `src/app/office/slides/html_render.spl`
- IDE slide probe: `src/app/ide/slides_compat.spl`
- HTML UI editor: `src/app/office/ui_editor.spl`
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

Designer/UI editing uses `app.office.ui_editor` as a pure HTML design document
substrate. It parses positioned frame/component records, renders a stable
`.office-ui-design` HTML surface with inspector metadata, exports nodes to
SDD-compatible tables, and guards label edits with expected-value checks.

Draw/diagram editing should prefer the SDD substrate in
`std.editor.services.sdn_graph` for geometry, layers, connector routes,
waypoints, anchors, rendered SVG connector paths, and pure edge reroute
operations. Legacy SVG shape helpers remain compatibility utilities, not the LLM
catalog owner for Draw.

IDE feature checks should expose these hardening markers in both TUI and GUI
modes:

- Markdown: `css_doc=true escaped=true`
- Slides: `ppt_html=true safe_css=true positioned=true`
- LLM catalog: Writer has `render-writer-markdown-html`; Impress has
  `render-ppt-markdown-html`; Draw is SDD-backed with
  `reroute-sdd-connector`; Designer has `render-ui-html`, `export-ui-sdd`, and
  `ui-label-edit`.

## Verification

Run each focused gate once per session:

```sh
bin/simple check \
  src/app/office/md_wysiwyg.spl \
  src/app/office/md_wysiwyg_gui.spl \
  src/app/office/slides/html_render.spl \
  src/app/office/ui_editor.spl \
  src/app/ide/markdown_render.spl \
  src/app/ide/slides_compat.spl \
  test/01_unit/app/office/md_wysiwyg_spec.spl \
  test/01_unit/app/office/md_wysiwyg_render_spec.spl \
  test/01_unit/app/office/slides/html_render_spec.spl \
  test/01_unit/app/office/ui_editor_spec.spl \
  test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl

SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/md_wysiwyg_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/slides/html_render_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/office/ui_editor_spec.spl
SIMPLE_LIB=src bin/simple test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple-interp src/app/ide/main.spl --feature-check --tui
bin/simple-interp src/app/ide/main.spl --feature-check --gui
bin/simple spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl --output doc/06_spec --no-index
find doc/06_spec -name '*_spec.spl' | wc -l
```

The layout guard must print `0`. Generated manuals live under `doc/06_spec`;
executable specs stay under `test/`.
