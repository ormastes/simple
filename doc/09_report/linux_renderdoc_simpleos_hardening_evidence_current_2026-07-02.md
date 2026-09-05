# Linux RenderDoc + SimpleOS Hardening Evidence

- status: pass
- scope: linux-renderdoc-web-gui-simpleos-qemu-wm-llvm-port-engine2d-simd-and-qemu-gpu-access
- evidence_date_local: 2026-07-02
- linux_renderdoc_source_report: `doc/09_report/linux_vulkan_render_log_compare_2026-06-29.md`
- vulkan_engine2d_source_report: `doc/09_report/vulkan_engine2d_readback_2026-07-03.md`
- cpu_simd_engine2d_source_report: `doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md`
- qemu_gpu_capture_source_report: `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-05.md`
- rv64_qmp_capture_source_report: `doc/09_report/rv64_display_smoke_qmp_evidence_current_2026-07-02.md`
- simpleos_source_report: `doc/09_report/simpleos_hardening_evidence_matrix_current_2026-07-02.md`
- simpleos_llvm_source_report: `doc/09_report/simpleos_llvm_port_evidence_current_2026-07-02.md`

## Linux RenderDoc/Vulkan

- command: `sh scripts/check/check-linux-vulkan-render-log-compare.shs`
- status: pass
- blocked_gate_count: 0
- simple_vulkan_gate_status: pass
- browser_backing_gate_status: pass
- pairwise_gate_status: pass
- argb_source_gate_status: pass
- renderdoc_gate_status: pass
- simple_rdoc_artifact_magic: RDOC
- chrome_rdoc_artifact_magic: RDOC
- electron_rdoc_artifact_magic: RDOC
- simple_rdoc_artifact: `build/renderdoc/canonical-probe/simple/simple_gui_app_capture.rdc`
- chrome_rdoc_artifact: `build/renderdoc/chrome-implicit-layer-default-autocapture/html/gpu_chrome_capture.rdc`
- electron_rdoc_artifact: `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc`

## Engine2D Vulkan Readback

- report: `doc/09_report/vulkan_engine2d_readback_2026-07-03.md`
- status: pass
- backend: vulkan
- present_exercised: true
- readback_exercised: true
- clear_status: pass
- clear_mismatches: 0
- rect_status: pass
- rect_mismatches: 0
- draw_image_device_readback_spec: `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
- draw_image_device_readback_status: pass
- draw_image_device_readback_examples: 7
- draw_image_clipped_readback_status: pass
- draw_image_clip_rect_readback_status: pass
- draw_image_mask_readback_status: pass
- software_facade_draw_image_clip_mask_status: pass
- software_facade_draw_image_transform_clip_mask_status: pass
- cpu_simd_facade_draw_image_clip_mask_status: pass
- cpu_simd_facade_draw_image_scaled_clip_mask_status: pass
- cpu_simd_facade_draw_image_transform_clip_mask_status: pass
- web_renderer_backend_parity_spec: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.spl`
- web_renderer_backend_parity_status: pass
- web_renderer_backend_parity_examples: 10
- web_renderer_backend_parity_failures: 0
- blur_or_tolerance_used: false
- vulkan_strict_exit_code: 0
- cpu_vulkan_parity_exit_code: 0

## CPU SIMD Engine2D Acceleration

- report: `doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md`
- status: pass
- arch: x86_64
- feature: avx2
- native_simd_executed: true
- native_simd_bit_exact: true
- native_simd_hits: 2
- provider_hits: 17
- fill_mismatch_count: 0
- copy_mismatch_count: 0
- alpha_mismatch_count: 0
- scroll_mismatch_count: 0
- diagram_mismatch_count: 0
- blur_or_tolerance_used: false

## QEMU GPU Capture Access

- live_x86_64_report: `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-05.md`
- live_rv64_report: `doc/09_report/rv64_display_smoke_qmp_evidence_current_2026-07-02.md`
- harness_report: `doc/09_report/qemu_capture_fake_qmp_evidence_current_2026-07-02.md`
- status: pass
- backend: qemu_live_vm
- x86_64_auto_qmp_status: pass
- x86_64_live_qmp_screendump_status: pass
- x86_64_live_capture_pixels: 786432
- x86_64_live_capture_sample_matches: 10
- x86_64_live_capture_sample_mismatches: 0
- x86_64_live_capture_full_scene_mismatches: 0
- qemu_guest_perf_sample_origin: qemu-guest
- rv64_qmp_screendump_status: pass
- rv64_qmp_dimensions: 320x240
- rv64_qmp_nonblack_pixels: 76800
- rv64_qmp_wm_anchor_matches: 5
- qemu_virtio_gpu_access: pass
- qemu_virtio_gpu_access_contract: `src/os/_QemuRunner/scenario_catalog.spl:scenario_riscv64_display_smoke`
- fake_qmp_harness_status: pass
- blur_or_tolerance_used: false

## SimpleOS QEMU/WM

- report: `doc/09_report/simpleos_hardening_evidence_matrix_current_2026-07-02.md`
- status: pass
- passed: 11/11
- executable_launch_from_fs: pass
- ssh_shell_smf_and_exec: pass
- shared_wm_logic: pass
- cpu_simd_engine2d_diagram: pass
- web_renderer_engine2d_bitmap: pass
- simple_gui_webrenderer_bitmap: pass
- production_gui_web_renderer_parity: pass
- qemu_host_counterpart_bitmap: pass
- qemu_gui_smf_artifact_contract: pass
- qemu_guest_perf_release_gate_status: pass
- qemu_guest_perf_harness_sample_origin: qemu-guest
- qemu_wm_simple_gui_mdi: pass
- qemu_wm_simple_gui_mdi_ppm_anchors: pass
- qemu_wm_simple_gui_mdi_input_status: pass
- rv64_display_smoke_qmp: pass
- rv64_display_smoke_qmp_width: 320
- rv64_display_smoke_qmp_height: 240
- rv64_display_smoke_qmp_anchor_matches: 5
- qemu_virtio_gpu_access: pass
- qemu_virtio_gpu_access_reason: rv64-qmp-virtio-gpu-display-smoke-pass

## SimpleOS LLVM Port

- report: `doc/09_report/simpleos_llvm_port_evidence_current_2026-07-02.md`
- status: pass
- x86_64_cross_clang_link_status: pass
- x86_64_cross_clang_driver_link_smoke: pass
- x86_64_compiler_rt_builtins_status: pass
- x86_64_lld_link_status: pass
- x86_64_sysroot_target_marker: `build/os/sysroot/share/simpleos/target-triple.txt`
- x86_64_sysroot_target_marker_status: pass
- aarch64_sysroot_archives_status: pass
- aarch64_cross_llvm_stage2_status: pass
- smoke_spec: `test/02_integration/os/port/llvm/smoke_clang_spec.spl`
- smoke_spec_status: pass
- smoke_spec_examples: 8
- smoke_spec_failures: 0

## Related Game2D Breakout Evidence

- status: pass_with_tracked_800x600_perf_gap
- wrapper: `scripts/check/check-game2d-breakout.shs`
- wrapper_overall: pass
- logic_session_spec: `test/03_system/game2d/breakout_production_spec.spl`
- logic_session_status: pass
- logic_session_examples: 1
- render_oracles_spec: `test/03_system/game2d/breakout_render_oracles_spec.spl`
- render_oracles_status: pass
- render_oracles_examples: 2
- render_oracles_lowres_frame_time_ms: 12
- render_oracles_target_800x600_budget_met: false
- headless_filled_rect_optimization: clipped direct framebuffer writes in `HeadlessBackend._draw_rect_filled`
- captures_spec: `test/03_system/game2d/breakout_captures_spec.spl`
- captures_status: pass
- captures_examples: 1
- captures_resolution: 160x120
- captures_ppm_count: 5
- captures_brick_hit_score_before: 0
- captures_brick_hit_score_after: 10
- window_capture_spec: `test/03_system/game2d/breakout_window_capture_spec.spl`
- window_capture_status: pass_with_gui_feature_driver
- window_capture_examples: 1
- window_capture_frames_presented: 12
- window_capture_binary: `src/compiler_rust/target/debug/simple`
- tracked_jit_render_gap: `doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`
- tracked_window_host_gap: `doc/08_tracking/bug/game2d_no_window_externs_in_host_binaries_2026-07-03.md`

## Related Game3D Rollball Evidence

- status: pass_with_tracked_800x600_perf_gap
- wrapper: `scripts/check/check-game3d-rollball.shs`
- wrapper_overall: pass
- driver: `src/app/game.rollball/game.spl`
- session_status: pass
- win_session_steps: 3600
- lose_session_steps: 3600
- win_state_status: pass
- lose_state_status: pass
- distinct_terminal_frames_status: pass
- motion_status: pass
- occlusion_status: pass
- camera_status: pass
- vulkan_backend_status: pass
- hud_status: pass
- ppm_count: 11
- perf_gap_status: tracked
- frame_p95_ms: not_measured_operation_limit
- frame_p95_target_ms: 33.0
- tracked_perf_gap: `doc/08_tracking/bug/cranelift_f32_trig_wrapper_codegen_2026-07-02.md`
- software_backend_unlit_fast_path: `SoftwareBackend3D.submit_triangle` skips world-space normal/lighting work for `MATERIAL_UNLIT`

## Related GUI Vulkan Window Evidence

- status: pass
- wrapper: `scripts/check/check-gui-vulkan-window.shs`
- wrapper_overall: pass
- binary: `src/compiler_rust/target/debug/simple`
- run: `SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src sh scripts/check/check-gui-vulkan-window.shs`
- render_size: 200x150
- compact_mode: `SHOWCASE_G1_1_COMPACT=1`
- renderer_log_line: `showcase_renderer_backend=vulkan;requested=vulkan;vulkan_device=requested=vulkan;selected=vulkan;status=Initialized;api=vulkan;gate=vulkan_runtime;shader=spirv;compute=true;graphics=true;present=false`
- render_completed: 1
- render_wait_secs: 52
- offscreen_ppm_bytes: 90015
- window_capture_attempts: 9
- window_capture_status: captured
- window_distinct_colors: 6
- assert_vulkan_backend: pass
- assert_vulkan_frame: pass
- assert_window_capture: pass
- assert_widget_content: pass
- widget_oracle_ink_coverage: 0.005066666666666664
- widget_oracle_required_ink_coverage: `> 0.005`
- spec: `test/03_system/check/gui_vulkan_window_spec.spl`
- spec_status: pass
- spec_examples: 6

## Scope Boundary

This report proves the Linux RenderDoc/web/gui, Vulkan Engine2D readback, CPU
SIMD Engine2D acceleration, QEMU screendump/readback access, SimpleOS QEMU/WM
hardening, and current LLVM-to-SimpleOS cross-toolchain slices only. It does
not claim Game2D production completion, macOS, Windows, iOS, Android, or
cross-platform freshness completion.
