# TL;DR: Graphical Markdown WYSIWYG rendering

Render markdown to pixels (headless PPM or a window) through the shared web
2D lane — markdown is converted to styled HTML, then painted via Engine2D.

```
.md ─ build_wysiwyg_view ─ wysiwyg_preview_pane → styled HTML
       (app/office/md_wysiwyg.spl)        │
                                          ▼
   simple_web_render_html_to_pixels_with_engine2d_backend(html, w, h, "cpu_simd")
       └ HTML parse → CSS cascade → block layout → paint → Engine2D backend
```

Commands:

```bash
# headless → PPM framebuffer (PAGE_W/PAGE_H override; default 900x760)
bin/simple run src/app/office/md_wysiwyg_ppm.spl notes.md /tmp/notes.ppm
# windowed (window only when SIMPLE_GUI=1, else headless no-op)
SIMPLE_GUI=1 bin/simple run src/app/office/md_wysiwyg_gui.spl notes.md
```

- MD→HTML: `lib/common/markdown/render.spl` (`render_markdown_line_styled_html`)
- Styles: `lib/common/render_scene/office_style_resolver.spl`
- HTML→pixels: `lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`
- Oracle spec: `test/01_unit/app/office/md_wysiwyg_render_spec.spl` (pixel-count +
  non-bg ink + absolute black glyph color + distinct-md→distinct-framebuffer)

Full guide: [md_wysiwyg_graphical_render.md](md_wysiwyg_graphical_render.md).
