# Simple Web GPU Paint Offload Matrix Spec

Source: `test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl`

This perf/evidence spec checks the Simple Web GPU paint decision without
requiring local GPU hardware:

- solid-only frames skip CPU paint and may offload when transfer cost wins;
- mixed text/solid frames do not claim offload because CPU ground truth is still
  required for residual parity;
- many tiny solid fills are rejected when command traffic is more expensive than
  the upload-bound path.

The hardware device-readback proof remains in the Engine2D backend evidence
gates; this spec only guards the CPU-work and communication-overhead policy.
