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

## Resolved (2026-07-03) — native no-mirror fast path

- `Engine2D.create_with_backend_fast()` (src/lib/gc_async_mut/gpu/engine2d/engine.spl)
  shrinks the Metal CPU mirror to 1x1 (`MetalBackend.use_gpu_only()`), so draw
  ops forward to the GPU only. `Engine2D.read_pixels()` is now checksum-free and
  `MetalBackend.read_pixels()`/`read_pixels_gpu_only()` download the framebuffer
  in ONE FFI hop: `rt_metal_buffer_download` (ptr) into rt_alloc'd host memory,
  then `rt_bytes_from_raw` marshals it to a packed Simple `[u8]` (return-value
  marshalling — the interpreter does NOT reflect Rust writes into passed-in
  `[u8]`/`[u32]` arrays, only the raw-ptr and return-value paths work), then a
  pure-arithmetic (no-FFI) `[u8]->[u32]` pack. The 393k-call read loop (~10 s)
  and the O(n) Simple readback checksum (~10 s) are both gone.
- `MetalBackend.set_clip` no longer poisons `gpu_frame_complete` for a
  full-framebuffer clip (a no-op); the layout Draw IR always emits exactly that,
  so the GPU frame stays authoritative. Real sub-framebuffer clips still fall
  back to the mirror.
- New entry `simple_web_layout_render_html_pixels_engine2d()`
  (src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl)
  and `wm_scene.render_scene_to_backend` routes desktop-res chrome through it.

### Measured (M4, interpreter, 1024x768, 12-window scene)
exec + one-shot readback ~1.4 s (was 17.9 s exec + 10.1 s readback ≈ 28 s).
Bit-exact vs the software mirror for in-bounds rect scenes. Evidence gate:
`scripts/check/check-engine2d-nomirror-fast-render-evidence.shs`. The
cpu-metal primitive parity gate stays `pass (cpu-metal-bitexact)`.
