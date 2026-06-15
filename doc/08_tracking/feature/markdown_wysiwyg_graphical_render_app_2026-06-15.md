# Feature Request: Wire markdown WYSIWYG to graphical (pixel) rendering

- **Date:** 2026-06-15
- **Area:** `app/office` (`md_wysiwyg`) + `lib/common/markdown` + `examples/06_io/ui` (web render)
- **Status:** open
- **Priority:** medium

## Context

Graphical markdown rendering is implemented as a 3-layer composition, and every
layer works in isolation — but the last wire (markdown → graphical preview *app*)
is missing.

What exists and works today:

1. **Markdown → styled HTML** — `src/lib/common/markdown/render.spl`
   `render_markdown_line_styled_html(line)` emits `<h{n}>/<p>` with inline CSS
   resolved from the office style resolver.
2. **Style cascade** — `src/lib/common/render_scene/office_style_resolver.spl`
   (`resolve_style` + `style_to_css_text`); shared by markdown, Writer, Impress.
3. **HTML → pixels (web backend)** —
   `simple_web_render_html_to_pixels_with_engine2d_backend(html, w, h, backend)`
   in `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`, backed
   by the real HTML parse → CSS cascade → block layout → paint pipeline in
   `simple_web_html_layout_renderer.spl`, dispatched over Engine2D backends.
4. **WYSIWYG editor model** — `src/app/office/md_wysiwyg.spl`
   (`build_wysiwyg_view`, `wysiwyg_update_line`, `wysiwyg_preview_pane`) produces
   editable source ↔ rendered-HTML line pairs and an incremental re-render path.

The IDE markdown preview itself renders only to **TUI ANSI text**
(`src/lib/editor/render/md_renderer.spl`); it never touches the web backend.

## The gap

There is **no app** that takes the WYSIWYG `wysiwyg_preview_pane(view)` HTML and
feeds it through `simple_web_render_html_to_pixels_with_engine2d_backend(...)`
into a window or PPM. The two existing graphical entrypoints —
`examples/06_io/ui/web_render_file_gui.spl` and
`examples/06_io/ui/web_render_page_ppm.spl` — accept **HTML only**, not raw
markdown. So markdown cannot be rendered graphically end-to-end without a manual
MD→HTML pre-conversion step. Office Writer/Impress already do this glue with their
own HTML; markdown just needs the same ~3-line hookup.

## Ask

Provide an end-to-end graphical markdown path. Either:

1. A dedicated `src/app/office/md_wysiwyg_gui.spl` (window) +
   `md_wysiwyg_ppm.spl` (headless) that builds a `WysiwygView` from a `.md` file,
   wraps it via `wysiwyg_preview_pane`, and renders through
   `simple_web_render_html_to_pixels_with_engine2d_backend`; OR
2. Extend `web_render_file_gui.spl` / `web_render_page_ppm.spl` to detect a `.md`
   argument and pre-convert via `render_markdown_line_styled_html` before render.

Include a rendering sanity spec (PPM framebuffer / `expect_draw` with an absolute
oracle, per the SPipe rendering-check rules) proving markdown actually paints —
not a screenshot-only or `expect(true)` placeholder.

## Files

- `src/app/office/md_wysiwyg.spl` (model — done)
- `src/lib/common/markdown/render.spl`, `.../utilities.spl` (MD→HTML — done)
- `src/lib/common/render_scene/office_style_resolver.spl` (styles — done)
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl` (HTML→pixels — done)
- `examples/06_io/ui/web_render_file_gui.spl`, `web_render_page_ppm.spl` (HTML-only — to extend)
- NEW: `src/app/office/md_wysiwyg_gui.spl` / `md_wysiwyg_ppm.spl` (the missing glue)

## Related

- `editor_markdown_editing_subsystem_2026-05-28.md` (TUI markdown subsystem)
- `engine2d_trait_facade_backend_execution_2026-06-02.md` (Engine2D backend dispatch)
