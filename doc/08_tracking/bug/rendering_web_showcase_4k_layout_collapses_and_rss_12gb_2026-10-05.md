# rendering_web showcases at 3840x2160: layout collapses, `status=pass`, 12 GB RSS

- **Filed:** 2026-10-05
- **Area:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`
  (`simple_web_layout_render_html_pixels_engine2d_with_images`). This code is
  owned by the browser_engine lane and was not edited here.
- **Status:** OPEN, routed to the browser_engine owner

## Symptom

Same seed and same tree, JIT, Vulkan backend:

| entry | size | wall | max RSS | frame |
|---|---|---|---|---|
| rendering_web_core | 960x640 | 55 s | 2.76 GB | correct; byte-identical to the interpreter |
| rendering_web_core | 1920x1080 | 47 s | 6.51 GB | correct; content column ~1050 px wide |
| rendering_web_core | 3840x2160 | 39 s | 5.82 GB | **nearly blank**: one ~190x90 px box top-left |
| rendering_web_extended | 3840x2160 | 40 s | **12.36 GB** | **collapsed layout**: blocks shrink to narrow columns and text overlaps |

Both 4K runs print `showcase status=pass`. The example's only gates are
`pixels.len() == w*h` and `checksum != 0`, so a near-blank frame passes. That
false pass is part of the bug.

## Repro

```
SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160 SIMPLE_TIMEOUT_SECONDS=0 \
SIMPLE_SHOWCASE_CAPTURE=/tmp/web_core_4k.ppm \
<seed> run examples/06_io/ui/rendering/rendering_web_core.spl
```

## Not yet established

- JIT and interpreter are byte-identical at 960x640. A 4K interpreter run was
  not taken because of its memory cost, so a JIT-only cause at 4K is not ruled
  out.
- RSS grows with the viewport much faster than the framebuffer does. The 4K
  ARGB frame is 33 MB, yet the run uses 5.8 to 12.4 GB.
