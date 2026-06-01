# GUI Color/Image Pipeline 8K Evidence

- status: pass
- surface: 7680x4320 BGRA8
- framebuffer_bytes: 132710400
- lab_xyz_full_frame_bytes: 796262400
- packed_hot_path: true
- default_semantic_space: cielab
- connection_space: cie_xyz
- lazy_startup: color transforms, TIFF decoder, and JPEG XL decoder are not initialized by the 8K surface plan
- red_lab_xyz_argb_roundtrip: true
- pure_simple_tiff_pixels: covered by focused raster spec for strips, tiles, PackBits, planar, high-bit-depth, palette, gray, RGB/RGBA, and Lab-like paths
- pure_simple_jpegxl_stage: metadata parsing, sparse 8K placeholder allocation, structured default-sRGB color metadata, non-default structured color fail-closed routing, and exact raster tiling are covered; full JPEG XL pixel decode remains a follow-up
- non_identity_icc_fail_closed: focused image decode spec requires RGB ICC profiles with Lab PCS to return icc-rgb-lab-transform-pending rather than identity pixels
- jpegxl_nondefault_color_fail_closed: focused image decode spec requires non-default JPEG XL structured color headers to return jpegxl-structured-color-transform-pending rather than silently accepting default sRGB

## Evidence

- gui_color_image_pipeline_8k_status=pass
- gui_color_image_pipeline_8k_width=7680
- gui_color_image_pipeline_8k_height=4320
- gui_color_image_pipeline_8k_bytes_per_pixel=4
- gui_color_image_pipeline_8k_framebuffer_bytes=132710400
- gui_color_image_pipeline_8k_lab_xyz_full_frame_bytes=796262400
- gui_color_image_pipeline_8k_uses_packed_hot_path=true
- gui_color_image_pipeline_8k_initializes_color_transforms=false
- gui_color_image_pipeline_8k_initializes_tiff_decoder=false
- gui_color_image_pipeline_8k_initializes_jpegxl_decoder=false
- gui_color_image_pipeline_8k_default_semantic_space=cielab
- gui_color_image_pipeline_8k_connection_space=cie_xyz
- gui_color_image_pipeline_8k_rgb565_uses_packed_hot_path=false
- gui_color_image_pipeline_8k_red_argb=4294901760
- gui_color_image_pipeline_8k_red_roundtrip_ok=true
- gui_color_image_pipeline_8k_lab_white_point=D65

## Focused Specs

    spec_path=examples/browser/test/gpu/surface_color_plan_spec.spl
    Simple Test Runner v1.0.0-beta
    
    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────
    
    Running: examples/browser/test/gpu/surface_color_plan_spec.spl
    [1/1] examples/browser/test/gpu/surface_color_plan_spec.spl
      [32mPASSED[0m (317ms)
    
    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    [32mPassed: 2[0m
    Failed: 0
    Duration: 320ms
    
    [32m✓ All tests passed![0m
    
    Slowest tests:
           317ms  examples/browser/test/gpu/surface_color_plan_spec.spl
    spec_exit_code=0
    spec_path=test/unit/lib/common/color/color_lab_xyz_spec.spl
    Simple Test Runner v1.0.0-beta
    
    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────
    
    Running: test/unit/lib/common/color/color_lab_xyz_spec.spl
    [1/1] test/unit/lib/common/color/color_lab_xyz_spec.spl
      [32mPASSED[0m (125ms)
    
    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    [32mPassed: 4[0m
    Failed: 0
    Duration: 130ms
    
    [32m✓ All tests passed![0m
    
    Slowest tests:
           125ms  test/unit/lib/common/color/color_lab_xyz_spec.spl
    spec_exit_code=0
    spec_path=examples/browser/test/paint/image_decode_spec.spl
    Simple Test Runner v1.0.0-beta
    
    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────
    
    Running: examples/browser/test/paint/image_decode_spec.spl
    [1/1] examples/browser/test/paint/image_decode_spec.spl
      [32mPASSED[0m (616ms)
    
    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    [32mPassed: 74[0m
    Failed: 0
    Duration: 622ms
    
    [32m✓ All tests passed![0m
    
    Slowest tests:
           616ms  examples/browser/test/paint/image_decode_spec.spl
    spec_exit_code=0
    spec_path=examples/browser/test/gpu/tiff_image_raster_spec.spl
    Simple Test Runner v1.0.0-beta
    
    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────
    
    Running: examples/browser/test/gpu/tiff_image_raster_spec.spl
    [1/1] examples/browser/test/gpu/tiff_image_raster_spec.spl
      [32mPASSED[0m (519ms)
    
    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    [32mPassed: 17[0m
    Failed: 0
    Duration: 525ms
    
    [32m✓ All tests passed![0m
    
    Slowest tests:
           519ms  examples/browser/test/gpu/tiff_image_raster_spec.spl
    spec_exit_code=0
