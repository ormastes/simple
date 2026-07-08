# Simple Web GPU Paint Offload Matrix Spec

Source: `test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl`

This perf/evidence spec checks the Simple Web GPU paint decision without
requiring local GPU hardware:

- solid-only frames skip CPU paint and may offload when total CPU+transfer cost
  wins;
- mixed text/solid frames do not claim offload because CPU ground truth is still
  required for residual parity;
- many tiny solid fills are rejected when command traffic does not beat the
  upload-bound total cost;
- no-op and offscreen fill-command frames do not claim offload just because CPU
  paint was skipped.

The hardware device-readback proof remains in the Engine2D backend evidence
gates; this spec only guards the CPU-work plus communication-overhead policy.
