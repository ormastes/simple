# Metal Engine2D Framebuffer Readback Evidence

- status: pass
- reason: raw-metal-framebuffer-download-proven
- platform: Darwin
- backend: src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl
- sffi: src/lib/nogc_sync_mut/io/metal_sffi.spl
- spec: test/02_integration/rendering/metal_engine2d_readback_spec.spl
- spec_status: pass
- gpu_download_path_present: true
- gpu_completeness_guard_present: true
- gpu_download_binding_present: true
- gpu_download_attempted: true
- gpu_readback_available: true
- exact_gpu_claimed: true
- blur_or_tolerance_used: false
- future_native_proof_required: false
- required_gate: test/02_integration/rendering/metal_engine2d_readback_spec.spl

This report gates the Engine2D Metal readback claim on a raw framebuffer
download through the runtime pointer ABI. CPU-only drawing operations still
invalidate GPU completeness and fall back to the software mirror.

## Evidence
- metal_engine2d_framebuffer_readback_status=pass
- metal_engine2d_framebuffer_readback_reason=raw-metal-framebuffer-download-proven
- metal_engine2d_framebuffer_readback_platform=Darwin
- metal_engine2d_framebuffer_readback_backend=src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl
- metal_engine2d_framebuffer_readback_sffi=src/lib/nogc_sync_mut/io/metal_sffi.spl
- metal_engine2d_framebuffer_readback_spec=test/02_integration/rendering/metal_engine2d_readback_spec.spl
- metal_engine2d_framebuffer_readback_spec_status=pass
- metal_engine2d_framebuffer_gpu_download_path_present=true
- metal_engine2d_framebuffer_gpu_completeness_guard_present=true
- metal_engine2d_framebuffer_gpu_download_binding_present=true
- metal_engine2d_framebuffer_gpu_download_attempted=true
- metal_engine2d_framebuffer_gpu_readback_available=true
- metal_engine2d_framebuffer_exact_gpu_claimed=true
- metal_engine2d_framebuffer_blur_or_tolerance_used=false
- metal_engine2d_framebuffer_future_native_proof_required=false
- metal_engine2d_framebuffer_required_gate=test/02_integration/rendering/metal_engine2d_readback_spec.spl

## Spec Log
    Simple Test Runner v1.0.0-beta

    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────

    Running: test/02_integration/rendering/metal_engine2d_readback_spec.spl
    [1/1] test/02_integration/rendering/metal_engine2d_readback_spec.spl
      [32mPASSED[0m (403ms)

    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    [32mPassed: 2[0m
    Failed: 0
    Duration: 514ms

    [32m✓ All tests passed![0m

    Slowest tests:
           403ms  test/02_integration/rendering/metal_engine2d_readback_spec.spl
