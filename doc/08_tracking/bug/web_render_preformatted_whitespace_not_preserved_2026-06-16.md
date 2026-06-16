# Bug: web renderer flattens preformatted / code-block whitespace

- **Id:** web_render_preformatted_whitespace_not_preserved_2026-06-16
- **Status:** open
- **Priority:** P2
- **Area:** `lib/common/markdown` (line renderer) + `lib/gc_async_mut/gpu/browser_engine` (web renderer)
- **Found via:** rendering `md_wysiwyg_graphical_render_tldr.md` (which contains a fenced pipeline diagram) to PPM

## Symptom

A fenced code block / ASCII pipeline diagram in the markdown rendered with its
indentation and alignment collapsed — the `.md → build_wysiwyg_view → …` diagram
lost its leading whitespace and monospace column alignment, so the box-drawing
layout reads as flat wrapped prose.

## Root cause (two layers)

1. **Markdown layer:** `render_markdown_line_styled_html` (lib/common/markdown/
   render.spl) styles each source line as a `<p>` paragraph; fenced-code lines
   (between ```` ``` ````) are not wrapped in `<pre>`/`<code>` nor given
   `white-space: pre`, so the structure that would preserve spacing is never
   emitted.
2. **Renderer layer:** the web layout renderer collapses runs of whitespace in
   normal flow (expected for HTML), and has no `white-space: pre` / `<pre>` path
   to suppress that collapse, so even a correctly-tagged block would still flatten.

## Expected

Fenced code blocks render in a monospace box with leading whitespace and internal
column spacing preserved (CSS `white-space: pre`), matching how the TUI renderer
already treats code blocks.

## Fix sketch

- markdown: emit fenced blocks as `<pre><code>…</code></pre>` (escaped), styled
  `white-space: pre; font-family: monospace` via `office_style_resolver`.
- renderer: honor `white-space: pre` — do not collapse spaces, break only on `\n`.

## Impact

Code samples and ASCII diagrams in markdown/HTML lose their formatting in the
raster output. The WYSIWYG line model also treats each line independently, so
fence state across lines is not yet tracked.
