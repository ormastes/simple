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
## UPDATE (2026-07-05) — dominant cost was O(n^2) JSON build, not marshalling; 6-7min → ~4-5s

Per-phase profiling of `tools/pixel_compare/render_simple_html.spl` at 320x240
metal (interpreter, Apple M4) showed the ~6-7 minute wall time was **dominated
by `_pixels_json`**, not `draw_image` marshalling:

- `_pixels_json` built the pixel JSON by pushing 76,800+ elements onto a
  growing `StringBuilder.parts` array — each push clones the array under the
  interpreter → **O(n^2)**; never finished in >90s.
- The GPU render itself (layout + present + `device_readback`) is ~2.3s; the
  per-pixel `draw_image` pack + per-8-byte readback loops at 320x240 complete
  in ~4.85s total even without the one-call fast path.

### Fixes

1. **`_pixels_json` → pre-sized index-assign + one `join`** (O(n), ~170ms for
   76,800 px). Removed the local `StringBuilder` class.
   (`tools/pixel_compare/render_simple_html.spl`).
2. **Optional marshalling accel** (kept, gated): `rt_write_u32s_to_raw`
   bulk-upload extern (inverse of the pre-existing `rt_u32s_from_raw`) copies a
   `[u32]` block into the host buffer in one call. Wired in
   `backend_metal.spl _dispatch_metal_image` behind the existing
   `SIMPLE_ONE_CALL_READBACK` flag with the per-pixel loop as the default
   pure-Simple fallback (a pure data-copy primitive, no logic). Helps large
   (800x600+/Retina) frames; not needed at 320x240.

### Result

320x240 `css_boxes.html` metal render (fast path on): **~4.05s** (was 6-7min),
bit-exact checksum **329775811848360**, `engine2d_readback_source=device_readback
gpu_backend_used=true`. Slow path (no flag): ~4.85s, same checksum.

Status: OPEN → largely resolved for the gate; interpreter per-pixel loops at
very large physical resolutions remain the next lever (the one-call externs
address them when `SIMPLE_ONE_CALL_READBACK=1`).
