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
- jpegxl_nondefault_color_fail_closed: focused image decode spec requires direct, full-container, and split-partial non-default JPEG XL structured color headers to fail closed rather than silently accepting default sRGB

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

    spec_path=test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.spl
    Simple Test Runner v1.0.0-beta

    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────

    Running: test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.spl
    [1/1] test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.spl
      PASSED (5069ms)

    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    Passed: 2
    Failed: 0
    Duration: 5074ms

    ✓ All tests passed!

    Slowest tests:
          5069ms  test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.spl
    spec_exit_code=0
    spec_path=test/01_unit/lib/common/color/color_lab_xyz_spec.spl
    Simple Test Runner v1.0.0-beta

    ───────────────────────────────────────────────────────────────
    Test Discovery
    ───────────────────────────────────────────────────────────────
      Spec files (*_spec.spl):  1
      Test files (*_test.spl):  0
    ───────────────────────────────────────────────────────────────

    Running: test/01_unit/lib/common/color/color_lab_xyz_spec.spl
    [1/1] test/01_unit/lib/common/color/color_lab_xyz_spec.spl
      PASSED (3457ms)

    ═══════════════════════════════════════════════════════════════
    Test Summary
    ═══════════════════════════════════════════════════════════════
    Files: 1
    Passed: 4
    Failed: 0
    Duration: 3460ms

    ✓ All tests passed!

    Slowest tests:
          3457ms  test/01_unit/lib/common/color/color_lab_xyz_spec.spl
    spec_exit_code=0
