# Markdown Document Decoration

Markdown preview supports document-level decoration for CSS-aware page rendering.
Decorations are read from frontmatter and fenced CSS blocks, then applied by the
GUI document renderer.

## Frontmatter

```markdown
---
page_view: true
header: Release Note
footer: Page 1
css_file: ./modern.css
---

# Title

Body
```

Fields:

- `layout` selects the document surface: `paper`, `ppt`, `slides`,
  `sheet`, `excel`, or `spreadsheet`.
- `page_view` enables page-style GUI rendering.
- `header` renders document header text.
- `footer` renders document footer text.
- `css_file` imports an external stylesheet.

## Inline CSS

Use fenced `css` or `style` blocks for document-local CSS:

````markdown
```css
.md-page-view {
    max-width: 72ch;
}
```
````

The block model marks these fences as `md_css`. TUI preview shows a compact CSS
marker, while GUI document preview emits a `<style class="md-inline-css">`
element.

## GUI Document Rendering

`gui_render_markdown_document(content)` renders a decorated Markdown document.
When `page_view: true`, output includes:

- `md-document page-view` root class.
- `md-page-view` article wrapper.
- `md-page-header`, `md-page-body`, and `md-page-footer` regions.
- Optional external stylesheet link from `css_file`.
- Optional inline CSS collected from CSS fences.

The body rendered inside `md-page-body` excludes frontmatter and CSS fences, so
document decoration does not leak into visible content.

## Paper Layout

Use `layout: paper` for Word-like page viewing and writing. The service model
keeps header, body, footer, external CSS, inline CSS, and script embeds as
separate render regions.

```markdown
---
layout: paper
header: Design Memo
footer: Draft
css_file: ./paper.css
---

# Design Memo

Body text.
```

`md_document_render_office_html(content)` emits `md-paper-layout`,
`md-page-header`, `md-page-body`, and `md-page-footer` regions.

## Presentation Layout

Use `layout: ppt`, `layout: slides`, or `layout: presentation` for slide-like
editing. Each level-two heading starts a page.

```markdown
---
layout: ppt
css_file: ./deck.css
---

## Intro @title
Welcome.

## Metrics
Numbers.
```

`md_document_split_ppt_pages(content)` returns one slide per `##` section.
`@name` labels on the slide heading become CSS classes such as `md-css-title`
in `md_document_render_ppt_html(content)`.

For editing, `md_document_replace_ppt_page(content, index, new_content)` rewrites
one slide body while preserving the surrounding `##` page boundaries.

## Spreadsheet Layout

Use `layout: sheet`, `layout: excel`, or `layout: spreadsheet` for Excel-like
table viewing. Markdown tables become addressable cells. Simple formulas can
reference cells and add values:

```markdown
---
layout: excel
---

| Name | Q1 | Q2 | Total |
|---|---:|---:|---:|
| Sales | 2 | 3 | =B2+C2 |
```

`md_document_sheet_cells(content)` maps table cells to addresses like `A1` and
`D2`. `md_document_render_sheet_html(content)` preserves raw formula metadata
and renders calculated values.

For editing, `md_document_replace_sheet_cell_value(content, address, value)`
rewrites one Markdown table cell. Re-reading the sheet model recalculates formula
cells such as `=B2+C2`.

## Script Embeds

Fenced `simple`, `spl`, and `script` blocks are script embeds. They are extracted
without executing them and rendered safely as code regions:

````markdown
```simple
print "hi"
```
````

`md_document_script_embeds(content)` returns the language and code for each
embed. `md_document_render_script_embeds_html(content)` escapes the code before
HTML output.

## MDSOC Boundary

The document interpretation lives in `std.editor.services.md_document_decor`.
GUI backend code delegates to this service for office-style layouts instead of
embedding parsing logic in the backend. This keeps plugin and renderer wiring
thin while the service owns Markdown-to-document-model transforms.
