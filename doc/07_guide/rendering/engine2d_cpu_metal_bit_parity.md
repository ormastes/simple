# Engine2D CPU ↔ Metal Bit-Level Parity

The CPU (software/SIMD) backend and the Metal GPU backend must produce
**bit-identical** framebuffers for the same draw script. This is verified by a
dedicated gate, not by trusting per-backend readback specs.

## Gate

```sh
sh scripts/check-engine2d-cpu-metal-parity-evidence.shs
```

It runs `test/integration/rendering/engine2d_cpu_metal_parity_run.spl` via
`bin/simple run … --mode=interpreter` (the test runner currently segfaults when
the engine2d GPU module graph is imported, so this is a `run` harness, not a
`_spec`). The harness renders identical scenes on both backends, downloads each
backend's own framebuffer, and asserts pixel-exact equality.

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
(Vulkan, CUDA) have their own gradient kernels; aligning those is tracked
separately.
