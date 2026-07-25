# Engine2D CPU ↔ Metal Bit-Level Parity

The CPU (software/SIMD) backend and the Metal GPU backend must produce
**bit-identical** framebuffers for the same draw script. This is verified by a
dedicated gate, not by trusting per-backend readback specs.

## Gate

```sh
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
```

It runs `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl` via
`bin/simple run … --mode=interpreter` (the test runner currently segfaults when
the engine2d GPU module graph is imported, so this is a `run` harness, not a
`_spec`). The harness renders identical scenes on both backends, downloads each
backend's own framebuffer, and asserts pixel-exact equality.

The gate is valid only with self-hosted Simple provenance. It now selects
`bin/simple`, `release/*/simple`, `bin/release/*/simple`, or
`build/bootstrap/stage3/simple` by default and records
`engine2d_cpu_metal_parity_simple_bin`,
`engine2d_cpu_metal_parity_simple_bin_source`, and
`engine2d_cpu_metal_parity_simple_bin_status` in `parity.env`. Any
`src/compiler_rust/**` override fails before the harness runs with
`engine2d_cpu_metal_parity_reason=simple-bin-forbidden`; that output is a
blocked evidence row, not CPU/Metal parity proof.

Two guards prevent the false-greens this area has a history of:

- **Metal must run on the GPU.** Each scene asserts `gpu_frame_complete == true`
  so `read_pixels()` downloads the GPU framebuffer instead of returning the CPU
  mirror (which would make the comparison a software-vs-software tautology).
- **Two independent framebuffers.** The CPU and Metal framebuffers are produced
  by separate backend instances; neither side is ever compared against itself.

Pitfall observed while building the harness: passing a backend through a
`fn(any)` parameter copies it by value (the self-pass-to-free-fn mutation-loss
bug), so the GPU dispatch runs on a throwaway copy and the original reports
`gpu_frame_complete == false`. Render on concrete-typed backends.

## Canonical math: integer lerp

Opaque writes (`clear`, `draw_rect_filled`, `draw_rect` outline) are byte copies
and match trivially. The one divergence was **`draw_gradient_rect`**: the CPU
path used a float lerp while the Metal MSL kernel uses an integer lerp, so they
differed by ±1 per channel from rounding (960/1024 pixels mismatched on a 32×32
gradient).

A float gradient cannot be reproduced bit-exactly on the GPU. The fix
canonicalizes **both** backends to the same integer lerp the MSL kernel already
used:

```
out = a + (b - a) * row / max_t      # max_t = max(h - 1, 1), truncate toward zero
```

Simple's `i32` division truncates toward zero (e.g. `-255/31 == -8`), matching
C/MSL, so the CPU result is bit-identical to the GPU kernel including for the
negative intermediates that occur when a channel decreases down the gradient.

Scope note: this aligns the CPU and Metal backends only. Other GPU backends
(Vulkan, CUDA) have their own gradient kernels; the CUDA strict spec already
asserts the integer-lerp values this fix produces, and the CPU↔Vulkan parity
spec only compares CPU-vs-CPU paths, so neither regresses. The web/Chromium
parity gates do not render gradients (the HTML layout renderer has no gradient
path), so they are unaffected.

## Canonical math: primitive rasterization (line / circle / rounded_rect / triangle)

The primitive ops once used *different algorithms* on each backend (CPU
Bresenham/midpoint vs GPU per-pixel/distance-field), diverging by 24/92/532
pixels on a 32×32 scene, and `draw_triangle_filled` was never GPU-dispatched at
all. They are now all bit-exact on genuine GPU readback. The rule that makes this
possible: **the canonical algorithm must be expressible per-pixel so the GPU can
run it, and the CPU follows the same rule** (the gradient integer-lerp pattern,
generalized).

- **Filled shapes** get a per-pixel inclusion test, which is both clean and the
  natural GPU form:
  - `circle_filled`: `dx² + dy² ≤ r²`. The CPU emits it as one `isqrt(r² - dy²)`
    span per row, so it stays a fast hline fill yet matches the GPU pixel-for-pixel.
  - `triangle`: integer barycentric (edge-function / 2× area); inside when all
    three weights share the sign of the determinant. GPU dispatch is now enabled
    (`_dispatch_metal_triangle`), so it is no longer a CPU-mirror tautology.
- **Thin shapes keep the higher-quality CPU algorithm (Bresenham / midpoint) and
  the GPU reproduces it by recurrence-replay** — do *not* swap them for a
  per-pixel distance field, which gaps at shallow line angles and at circle
  diagonals (that would trade quality for parity). Each GPU thread replays the
  integer recurrence to *its* step and writes that step's pixel(s):
  - `line`: thread `t` replays `t` iterations of the `sw_bresenham` error loop
    (1D dispatch, `steps+1` threads); thickness offsets translate the whole line.
  - `circle` outline: thread `i` replays `i` midpoint iterations and emits the 8
    symmetric pixels (1D dispatch, `r+1` threads, extras self-cull on `px < py`).
  - `rounded_rect`: the MSL kernel was a *filled interior* test — a real shape
    bug vs the CPU outline. It now draws the outline: straight edges plus the
    four midpoint corner arcs replayed to match `sw_corner_arc` (1D dispatch,
    `max(w,h)` threads).

Replay is O(extent) per thread, but these primitives are small and are not the
fill-rate bottleneck (filled/blit/gradient stay O(1) per pixel), so the cost is
not a concern. The CPU triangle did move from O(height) scanline to O(bbox-area)
barycentric — negligible for UI-sized triangles, noticeable for very large ones.

## What is bit-exact (measured)

All gate scenes are bit-exact CPU↔Metal on genuine GPU readback
(`gpu_frame_complete=true`, `mismatches=0/1024`): `clear`, `draw_rect_filled`,
`draw_rect` (outline), `draw_gradient_rect`, `draw_line`, `draw_circle`
(+filled), `draw_rounded_rect`, `draw_triangle_filled`.

### False-green guard: MATCH ≠ correct

Because the harness clears-then-draws, an op that renders *nothing* (or the same
wrong shape on both backends) still yields two equal buffers and prints `MATCH` —
indistinguishable from all-black-vs-all-black. Equality alone is not proof. When
a primitive's algorithm changes on **both** sides at once (here `circle_filled`
and `triangle`), also run an *absolute* check: a filled shape's center/centroid
must equal the draw color and a far pixel must equal the background, on both the
CpuBackend and the MetalBackend. Only then is `MATCH` correct-vs-correct.

Resolution and the (pre-existing, separate) CUDA cross-backend note are tracked in
`doc/08_tracking/bug/engine2d_cpu_metal_primitive_raster_divergence_2026-06-03.md`.
