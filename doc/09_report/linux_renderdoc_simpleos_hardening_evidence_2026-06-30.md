# Linux RenderDoc + SimpleOS Hardening Evidence

- status: pass
- scope: linux-renderdoc-web-gui-and-simpleos-qemu-wm
- evidence_date_local: 2026-06-30
- evidence_date_utc: 2026-06-29

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
- simple_rdoc_artifact: `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/simple_gui_app_capture.rdc`
- chrome_rdoc_artifact: `build/renderdoc/chrome-implicit-layer-default-autocapture/html/gpu_chrome_capture.rdc`
- electron_rdoc_artifact: `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc`

## Chrome/Corpus Guard

- command: `sh scripts/check/check-gui-hardening-open-gates.shs`
- status: pass
- report: `doc/09_report/gui_hardening_open_gates_2026-06-29.md`
- browser_corpus_specs: pass

## SimpleOS QEMU/WM

- report: `doc/09_report/simpleos_hardening_evidence_matrix_2026-06-29.md`
- status: pass
- passed: 9/9
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
- qemu_wm_simple_gui_mdi_ppm_nonblack: 779590

## Scope Boundary

This report proves the Linux RenderDoc/web/gui and SimpleOS QEMU/WM hardening
slice only. It does not claim macOS, Windows, iOS, Android, or cross-platform
freshness completion.
