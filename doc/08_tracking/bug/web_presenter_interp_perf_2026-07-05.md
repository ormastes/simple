---
id: web_presenter_interp_perf_2026-07-05
status: OPEN
severity: high
discovered: 2026-07-05
discovered_by: Profiling tools/pixel_compare/render_simple_html.spl under check-macos-metal-browser-backing-evidence.shs
related: tools/pixel_compare/render_simple_html.spl
related: src/lib/common/web/render_scene.spl
related: src/lib/nogc_sync_mut/ffi/ffmpeg.spl
---

# Web presenter interpreter performance: ~6-7 minutes per 320x240 frame

## Summary

One 320×240 HTML frame rendered through the core web renderer under the interpreter takes **6–7 minutes** in tools/pixel_compare/render_simple_html.spl. This makes test gates impractically slow.

## Breakdown

- Layout: 2–6 seconds (layout algorithm itself)
- Draw/marshalling/readback: remaining ~5–6.5 minutes

The bottleneck is interpreted `draw_image` marshalling (pixel-by-pixel SFFI calls) + readback checksum computation + JSON string building.

## Context

Observed during:
```bash
scripts/check/check-macos-metal-browser-backing-evidence.shs
```

This gate exercises web rendering fidelity (Simple vs. Electron), but the interpreter path is too slow for practical test-run turnaround.

## Scope

**Performance regression class** — gates using the interpreter for web rendering become impractical. Native-compiled or JIT-compiled paths likely perform adequately, but interpreter overhead on pixel-loop operations is severe.

## Related

Requires investigation of:
- `draw_image` SFFI marshalling hot-path optimization
- Possible loop unrolling or batch marshalling in readback
- Whether native/JIT compilation path is acceptable as a workaround for this gate
