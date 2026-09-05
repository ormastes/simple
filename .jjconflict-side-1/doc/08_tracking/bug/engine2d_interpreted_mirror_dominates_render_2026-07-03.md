# Perf: Engine2D per-op interpreted mirror makes every backend equally slow

- **Date:** 2026-07-03
- **Severity:** high (blocks WM-chrome-via-CSS at desktop resolution; goal item)
- **Area:** src/lib/gc_async_mut/gpu/engine2d (Engine2D dispatch/mirror), draw_ir_adv executor

## Measurements (M4, interpreter, 1024x768, 12-window WM-like HTML scene, 64 draw-ir commands)
- HTML layout + Draw IR generation: ~0.9-1.1s (flat across resolutions — per-node)
- Software paint (layout renderer `paint`): 30.5s at 1024x768 (~39us/px), 50s with 12 windows
- Draw IR executed on Engine2D: exec 17.7-17.9s + read_pixels 10.1-10.2s —
  **identical for backend=software, cpu_simd, and metal**, proving the
  per-op interpreted framebuffer mirror is the entire cost; native NEON/GPU
  work is either skipped or invisible next to it.

## Consequence
The wm_scene CSS chrome path is capped at 10,000 px
(WM_SCENE_CSS_RENDER_PIXEL_CAP) purely because of this; layout itself is
cheap. Precedent fix: MetalBackend.use_gpu_only() (wm fullscreen demo)
shrinks the mirror to 1x1 and reads back from the GPU once per frame.

## Fix direction
1. Engine2D no-mirror/gpu-only mode: forward ops to the native backend only,
   one-shot readback from native/GPU buffer (marshalled in Rust, not an
   interpreted per-element copy loop).
2. Then: simple_web_layout_render_html_pixels via Draw IR + Engine2D
   (native), and raise/remove the wm_scene CSS cap.
