# Guide: Graphical Markdown WYSIWYG rendering

How to render markdown to pixels (headless PPM or a window) through the shared
2D API, and how the common / web / text renderers relate.

## Quick start

Headless (writes a PPM framebuffer):

```bash
# render a .md file to a .ppm
bin/simple run src/app/office/md_wysiwyg_ppm.spl notes.md /tmp/notes.ppm
# size via env (defaults 900x760)
PAGE_W=1200 PAGE_H=900 bin/simple run src/app/office/md_wysiwyg_ppm.spl notes.md out.ppm
```

Windowed (opens a window only when `SIMPLE_GUI=1`, else headless no-op):

```bash
SIMPLE_GUI=1 bin/simple run src/app/office/md_wysiwyg_gui.spl notes.md
```

Both build a `WysiwygView` from the markdown, wrap it via `wysiwyg_preview_pane`
(styled HTML), and render it with
`simple_web_render_html_to_pixels_with_engine2d_backend(html, w, h, "cpu_simd")`.

## The pipeline

```
.md text
  └─ build_wysiwyg_view            (app/office/md_wysiwyg.spl)
       ├─ inside ``` fences → render_markdown_code_line_styled_html
       │     (<pre>, monospace, white-space:pre — indentation preserved)
       └─ otherwise → render_markdown_line_styled_html  (lib/common/markdown/render.spl)
            └─ resolve_style + style_to_css_text  (office_style_resolver.spl)
  └─ wysiwyg_preview_pane → HTML
       └─ simple_web_render_html_to_pixels_with_engine2d_backend
            └─ HTML parse → CSS cascade → block layout → paint
                 └─ Engine2D backend (lane chosen by SIMPLE_2D_BACKEND or auto)
```

## Rendering fidelity

The web lane handles the cases markdown commonly hits (each covered by a case in
the render spec):

- **HTML entities** (`&amp; &lt; &gt; &quot; &#39;`) are decoded, so escaped
  characters paint as the real glyph, not a literal `&quot;`.
- **Long lines wrap** within the surface width instead of overflowing and
  clipping at the right edge.
- **Wrapped text reserves its full N-line height**, so a following block is
  placed below it (no overlap).
- **Fenced code blocks** render monospace and preformatted (`white-space: pre`)
  with leading indentation preserved; a leading `#` inside a fence stays code,
  not a heading.

## One 2D API, lane chosen by config/environment

There is a single `Engine2D` API. Which lane runs it — SIMD CPU vs a GPU backend
— is selectable without changing call sites:

```bash
SIMPLE_2D_BACKEND=cpu_simd  ...   # force the SIMD CPU lane
SIMPLE_2D_BACKEND=software  ...   # scalar reference
SIMPLE_2D_BACKEND=vulkan    ...   # GPU lane (falls back to auto-probe if it can't init)
```

The override is honored when the named backend initializes; otherwise the engine
auto-probes (priority: metal > cuda > rocm > … > cpu_simd > software > cpu).

## Three renderers, one shared base

- **common renderer** (`lib/common/render_scene`, `lib/common/ui/draw_ir`) —
  dependency-free style cascade + draw-IR primitives.
- **web renderer** (`browser_engine/simple_web_renderer.spl`) — HTML → pixels
  over Engine2D. Used by the MD WYSIWYG apps above.
- **text renderer / TUI** (`editor/render/md_renderer.spl`) — slim by default
  (no GPU imports), shares the same `office_style_resolver` cascade. For GPU
  offload, the opt-in `editor/render/md_draw_ir.spl` projects TUI lines into the
  same `DrawIrComposition` the GUI dispatches — so TUI can paint on the GPU lane
  too.

## Fonts

Unspecified text follows the current font-provider candidate policy; the
zero-config Engine2D path remains backend bitmap text. Explicitly specified
families use the same provider. CPU code owns glyph rasterization; supported GPU
lanes compose the resulting atlas, with CPU composition as the fallback.

## Rendering sanity specs

Prove markdown actually paints with an absolute pixel oracle (exact
`pixels.len() == w*h`, non-background count > 0, an absolute color invariant) —
never `expect(true)` or screenshot-only. See
`test/01_unit/app/office/md_wysiwyg_render_spec.spl` and the SPipe skill's
"Rendering Checks" section.
