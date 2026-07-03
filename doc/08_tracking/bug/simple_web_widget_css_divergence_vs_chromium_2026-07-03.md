# Finding: Simple web engine diverges structurally from Chromium on widget CSS

- **Date:** 2026-07-03
- **Severity:** high for "production level" widget rendering claims
- **Area:** simple web layout renderer draw-ir/engine2d lane (widget CSS features)
- **Gate:** scripts/check/check-widget-shells-crossengine-evidence.shs (exit 1, status=divergent)

## Measured (same HTML, generate_css("light") widget docs)
| fixture | Simple<->Chrome | Simple<->Electron | Chrome<->Electron |
|---|---|---|---|
| gui window 320x200 | 50.31% | 50.69% | **99.89%** |
| taskbar 480x64 | 47.01% | 47.12% | **99.93%** |
(non-text pixel agreement; per-channel tol <=8, sRGB-normalized, no blur;
glyph pixels excluded via Chrome DOM text mask)

## Finding
The two independent real browsers agree ~99.9% — the HTML/CSS is valid and
consistently rendered. The Simple lane renders a flat fill + single top border
where Chromium renders: border-radius (rounded cards/pill), box-shadow,
linear-gradient backgrounds, accent borders, and nested panel-content boxes.
Panel band top offset 8px (Simple y22 vs Chromium y14).

## Note on lanes
The SOFTWARE painter has rounded-rect/opacity machinery
(fb_rounded_rect_opacity_clip etc.), but the draw-ir lane emits plain
boxes (draw_ir_box_with_style -> RECT) with bg color only — radius, shadow,
gradient, and border props ride along as style strings and are not painted
by the engine2d executor. Closing this = teaching the draw-ir command set +
executor the missing box decorations (or routing widget docs through the
software painter's decorated path and uploading).

## Artifacts
build/widget_shells_crossengine/{simple,chrome,electron}_{window,taskbar}.png
+ report.md (2026-07-03 run).

## Also noted (pre-existing runtime gaps, not worked around silently)
- rt_string_builder_new extern unavailable in current self-hosted runtime
  (array-backed StringBuilder fallback used).
- Reading a binary PNG via std.io_runtime.file_read crashes the interpreter
  on rt_dir_exists.
