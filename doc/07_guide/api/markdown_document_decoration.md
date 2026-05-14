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
