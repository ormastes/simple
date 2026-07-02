# Bug: web-engine fast Metal lane renders text runs as solid bars, not glyphs

- **Date:** 2026-07-03
- **Severity:** medium (web-engine WM phase visually proves layout but text is unreadable)
- **Area:** Draw IR text command execution in Engine2D gpu-only fast mode

## Symptom
In the WM demo web-engine phase (html -> layout -> draw ir -> fast metal ->
present), text elements (window titles, content lines) appear as solid black
bars in the presented frame and in fullscreen_webengine.png. Rects, colors,
and layout geometry are correct (titlebar blue band check passes).

## Cause (suspected)
The Draw IR text command in the gpu-only fast lane is executed as a filled
rect (or the glyph path is skipped when the 1x1 mirror can't rasterize),
instead of routing to the existing GPU glyph path
(MetalBackend.draw_text_hires / kernel_blit_image, proven in the fit phase).

## Expected
Draw IR text commands in fast mode should rasterize glyphs via the existing
hi-res GPU text path (or CPU-glyph blit upload) so web-engine-rendered WM
text is readable.

## Evidence
build/wm_fullscreen_metal_evidence/fullscreen_webengine.png (2026-07-03
08:37 run, gate exit 0, webengine_capture_blue=ok).
