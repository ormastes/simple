# Metal Engine2D Framebuffer Readback Evidence

- status: unavailable
- reason: metal-requires-macos
- platform: Linux
- backend: src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl
- sffi: src/lib/nogc_sync_mut/io/metal_sffi.spl
- cpu_mirror_readback_used: true
- gpu_download_binding_present: true
- gpu_download_attempted: false
- gpu_readback_available: false
- exact_gpu_claimed: false
- blur_or_tolerance_used: false
- future_native_proof_required: true
- required_future_gate: darwin-native-compiled-metal-download-vs-cpu-mirror

This report is intentionally fail-closed: on non-macOS hosts it records
Metal as unavailable, and on macOS it fails until a native compiled proof
downloads the Metal framebuffer and compares it against the CPU mirror for
a deterministic vector-font/Engine2D scene.

## Evidence
- metal_engine2d_framebuffer_readback_status=unavailable
- metal_engine2d_framebuffer_readback_reason=metal-requires-macos
- metal_engine2d_framebuffer_readback_platform=Linux
- metal_engine2d_framebuffer_readback_backend=src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl
- metal_engine2d_framebuffer_readback_sffi=src/lib/nogc_sync_mut/io/metal_sffi.spl
- metal_engine2d_framebuffer_cpu_mirror_readback_used=true
- metal_engine2d_framebuffer_gpu_download_binding_present=true
- metal_engine2d_framebuffer_gpu_download_attempted=false
- metal_engine2d_framebuffer_gpu_readback_available=false
- metal_engine2d_framebuffer_exact_gpu_claimed=false
- metal_engine2d_framebuffer_blur_or_tolerance_used=false
- metal_engine2d_framebuffer_future_native_proof_required=true
- metal_engine2d_framebuffer_required_future_gate=darwin-native-compiled-metal-download-vs-cpu-mirror
