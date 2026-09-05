# Simple Web GPU Paint Offload Matrix Spec

Source: `test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl`

This perf/evidence spec checks the Simple Web GPU paint decision without
requiring local GPU hardware:

- backend selection treats `software`, `cpu`, and `cpu_simd` as CPU paths,
  treats `cuda`, `vulkan`, and `metal` as GPU paint candidates, and rejects
  unknown names instead of letting them masquerade as offload;
- the presenter route only enters GPU paint for measured winning frames, so
  CUDA/Vulkan/Metal solid-fill wins offload while CUDA/Vulkan/Metal
  command-overhead losers, CPU backends, unknown backends, and disabled GPU
  paint stay upload-bound with explicit CPU-job and speed route verdicts;
- solid-only frames skip CPU paint and may offload when total CPU+transfer cost
  wins, reporting `cpu-paint-offloaded` and `measured-gpu-faster`;
- residual-heavy fill frames may still offload when saved CPU paint makes total
  work win even though transfer alone loses;
- mixed text/solid frames do not claim offload because CPU ground truth is still
  required for residual parity, reporting `cpu-paint-required` and
  `not-offloaded`;
- many tiny solid fills are rejected when command traffic does not beat the
  upload-bound total cost, reporting `measured-gpu-slower-overhead`;
- exact break-even work stays CPU-bound instead of being reported as GPU
  offload;
- partial CPU savings still stay CPU-bound when total GPU paint work is more
  expensive than upload-bound work, also reporting
  `measured-gpu-slower-overhead`;
- no-op and offscreen fill-command frames do not claim offload just because CPU
  paint was skipped.

The hardware device-readback proof remains in the Engine2D backend evidence
gates; this spec only guards the CPU-work plus communication-overhead policy.
