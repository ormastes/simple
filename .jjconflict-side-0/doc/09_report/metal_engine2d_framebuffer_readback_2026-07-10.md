# Metal Engine2D Framebuffer Readback Evidence

- status: pass
- reason: raw-metal-framebuffer-download-proven
- platform: Darwin
- backend: src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl
- sffi: src/lib/nogc_sync_mut/io/metal_sffi.spl
- spec: test/02_integration/rendering/metal_engine2d_readback_spec.spl
- spec_status: pass
- simple_bin: bin/simple
- simple_bin_source: repo-self-hosted-fallback
- simple_bin_status: pass
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
- metal_engine2d_framebuffer_readback_simple_bin=bin/simple
- metal_engine2d_framebuffer_readback_simple_bin_source=repo-self-hosted-fallback
- metal_engine2d_framebuffer_readback_simple_bin_status=pass
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
    [memory-guard] SIMPLE_LIB=src contains 600+ .spl files — consider narrowing scope to avoid memory bloat
    Metal Engine2D framebuffer readback
      raw GPU pixels
        [32m✓ downloads clear and rect_filled pixels from the Metal framebuffer[0m
        [32m✓ stays GPU-complete after draw_text via the glyph-atlas kernel (GPU-dict use case #2, W4)[0m
        [32m✓ downloads draw_image pixels from the Metal framebuffer[0m
        [32m✓ blends a semi-transparent circle_filled identically on CPU mirror and Metal device (E1 fix)[0m
        [32m✓ blends a semi-transparent triangle_filled identically on CPU mirror and Metal device (E2 fix)[0m
        [32m✓ leaves the framebuffer unchanged for degenerate-dim draws on both lanes (E3/E4/E5 fix)[0m
    
    [32m6 examples, 0 failures[0m
    
    [33mwarning[0m: Deprecated syntax for type parameters
      --> /Users/ormastes/simple/src/lib/common/string_core.spl:89:44
       |
     89 |     while i < slen and is_whitespace_char(s[i]):
       |                                            ^
    
    Use angle brackets: s<...> instead of s[...]
    
    Run `simple migrate --fix-generics` to automatically update your code
    
    [33mwarning[0m: '#[runtime_intrinsics]' uses deprecated syntax, use '@runtime_intrinsics' instead
      --> /Users/ormastes/simple/src/lib/gc_async_mut/gpu/engine2d/backend_metal_runtime_ops.spl:1:1
       |
      1 | #[runtime_intrinsics]
       | ^
    
    Replace '#[runtime_intrinsics]' with '@runtime_intrinsics'
    
    [33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
      --> /Users/ormastes/simple/src/lib/gc_async_mut/env/platform.spl:3:1
       |
      3 | export use std.nogc_async_mut.env.platform.*
       | ^
    
    Use explicit exports instead
    
    Example: export use module.{A, B, C} or export A, B from module
    
    [33mwarning[0m: Deprecated syntax for type parameters
      --> /Users/ormastes/simple/src/lib/nogc_async_mut/path.spl:142:31
       |
    142 |         if c < bp.len() and pp[c] == bp[c]:
       |                               ^
    
    Use angle brackets: pp<...> instead of pp[...]
    
    Run `simple migrate --fix-generics` to automatically update your code
    
    [33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
      --> /Users/ormastes/simple/src/lib/gc_async_mut/io/metal_sffi.spl:3:1
       |
      3 | export use std.nogc_async_mut.io.metal_sffi.*
       | ^
    
    Use explicit exports instead
    
    Example: export use module.{A, B, C} or export A, B from module
    
    [memory-guard] SIMPLE_LIB=src contains 600+ .spl files — consider narrowing scope to avoid memory bloat
    [gc-warning] Higher-layer module 'std.nogc_sync_mut.gpu.engine2d.simd_provider' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
    [gc-warning] Higher-layer module 'std.nogc_sync_mut.gpu.engine2d.simd_kernels' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
    [gc-warning] Higher-layer module 'std.nogc_sync_mut.env.types' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
    [gc-warning] Higher-layer module 'std.nogc_sync_mut.io.metal_sffi' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
    
    
    =========================================
    Test Summary
    =========================================
    Files: 1
    Passed: 6
    Failed: 0
    Duration: 777ms
    
    PASS test/02_integration/rendering/metal_engine2d_readback_spec.spl
    [memory-guard] SIMPLE_LIB=src contains 600+ .spl files — consider narrowing scope to avoid memory bloat
    
