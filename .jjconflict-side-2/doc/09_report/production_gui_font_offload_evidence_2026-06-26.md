# Production GUI Font Offload Evidence

- status: pass
- reason: vector-and-bitmap-font-readback-matched
- vector backend: metal
- vector offload status: gpu-glyph-returned
- vector offload reason: metal-vector-font-glyph-pixels-returned
- vector readback status: vector-font-glyph-readback-matched
- vector readback reason: vector-font-gpu-readback-matched
- vector production ready: true
- bitmap backend: metal
- bitmap offload status: gpu-raster-plan-without-readback
- bitmap offload reason: bitmap-font-gpu-raster-kernel-ready-readback-required
- bitmap readback status: gpu-glyph-raster-readback-matched
- bitmap readback reason: bitmap-glyph-raster-gpu-readback-matched
- bitmap production ready: true
