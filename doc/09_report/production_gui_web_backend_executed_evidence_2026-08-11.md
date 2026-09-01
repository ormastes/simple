# Production GUI Web Backend-Executed Evidence

- status: unavailable
- reason: simple-bin-forbidden
- scene: backend-executed Engine2D clear/fill primitive proof
- dimensions: 16x16
- CPU SIMD resolved: 
- CPU SIMD total hits: 
- CPU SIMD alpha quality: 
- CPU SIMD alpha quality hits: 
- CPU SIMD different pixels: 
- Metal resolved: 
- Metal gpu frame complete: 
- Metal gpu readback pixel count: 
- Metal command queue handle: 
- Backend checksums (software/cpu_simd/metal/gpu):  /  /  / 
- Backend checksum match: 
- Same-frame backend readback: 
- Backend readback source: 
- Metal different pixels: 
- Software render elapsed us: 
- CPU SIMD render elapsed us: 
- Metal render elapsed us: 
- Total render elapsed us: 
- Software pixels/s: 
- CPU SIMD pixels/s: 
- Metal pixels/s: 
- Total pixels/s: 
- Timing budget us: 
- Timing budget status: 
- Timing budget reason: 
- Sample count: 
- Total elapsed us min/avg/max:  /  / 
- Total pixels/s min/avg/max:  /  / 
- First pixels (software/cpu_simd/metal/gpu):  /  /  / 
- Rect pixels (software/cpu_simd/metal/gpu):  /  /  / 
- blur/tolerance used: false

This evidence intentionally exercises the currently proven Metal GPU
readback subset (clear + filled rectangle) through Engine2D and separately
requires CPU-SIMD alpha blending to match the software renderer exactly.
It proves backend execution separately from the HTML layout fast path,
which currently renders through a pure framebuffer renderer. Larger
generated GUI scenes remain tracked as open Metal coverage.

## Raw Evidence
- production_gui_backend_status=unavailable
- production_gui_backend_reason=simple-bin-forbidden
- production_gui_backend_simple_bin=src/compiler_rust/target/bootstrap/simple
- production_gui_backend_simple_bin_source=explicit-env-rust-seed-forbidden
- production_gui_backend_simple_bin_status=forbidden

## Evidence Log
- production_gui_backend_status=unavailable
- production_gui_backend_reason=simple-bin-forbidden
- production_gui_backend_simple_bin=src/compiler_rust/target/bootstrap/simple
- production_gui_backend_simple_bin_source=explicit-env-rust-seed-forbidden
- production_gui_backend_simple_bin_status=forbidden
