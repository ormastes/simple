# Bug: web renderer flattens preformatted / code-block whitespace

- **Id:** web_render_preformatted_whitespace_not_preserved_2026-06-16
- **Status:** RESOLVED (2026-06-16)
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

## Fix

Both layers, contained:

1. **Markdown/WYSIWYG layer:** `build_wysiwyg_view` now tracks fenced-code state
   across lines (via `markdown_is_code_fence`): the ```` ``` ```` delimiters are
   hidden, and the lines between them render through a new
   `render_markdown_code_line_styled_html` that emits `<pre style="…code_block
   css…">` (monospace + `white-space: pre`) with the raw line — no heading or
   inline-markdown parsing, so a leading `#` stays code instead of becoming a
   giant `<h1>`.
2. **Renderer layer:** `white-space: pre` already mapped to
   `white_space_nowrap`, and `inherit_style` already propagates it to the child
   text node. The text measure and the painter now use the *untrimmed*
   `text_data` (not `text_trimmed`) for `white_space_nowrap` nodes, so leading
   indentation is preserved; normal flow is unchanged.

## Verification

`md_wysiwyg_render_spec.spl` gains a code-block test: an 8-space-indented code
line's first black glyph lands at column ~86 vs ~6 for an unindented code line
(indentation preserved; same glyph set). Internal column spacing is already
preserved by the painter. Regression suite `test/01_unit/browser_engine/`
unchanged (34 pass / 45 pre-existing fail). Note: long code lines do not wrap
(correct `white-space: pre` behavior) and may clip horizontally.
