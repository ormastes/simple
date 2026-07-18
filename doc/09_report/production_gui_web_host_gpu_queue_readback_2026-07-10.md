# Production GUI/Web Host-GPU Queue Readback Evidence

Date: 2026-07-10

## Summary

- linux GUI/web queue integration status: fail
- linux GUI/web queue integration reason: browser-frame-first-render-budget-not-met
- legacy compatibility status key: production_gui_web_host_gpu_queue_readback_status=fail
- legacy compatibility reason key: production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met
- full host-GPU platform matrix status: partial
- joined GUI/web device readback backend: vulkan
- missing device-readback platforms: rocm,directx,webgpu
- queue emission via rt_host_gpu_queue_emit: pass
- backend_code=0 drain result: unavailable
- nonzero backend-code drain result: pass
- nonzero backend-code payload receipt: pass
- nonzero backend-code payload text receipt: pass
- DirectX/WebGPU provenance guard: pass
- DirectX native gate: unavailable
- native readback wrapper SSpec coverage: pass
- native readback wrapper generated-doc evidence: pass
- queue overflow rejection: pass
- BrowserBackend frame queue bridge: fail
- BrowserBackend host event roundtrip: fail
- same-frame BrowserBackend Engine2D pixel readback receipt: pass
- same-frame Vulkan/BrowserBackend device readback receipt: pass
- browser input event to queued frame/readback correlation: pass
- runtime event receipt contract: pass
- backend readback handle contract: pass
- Engine2D readback metadata proof predicate: pass
- compiler HostGpuLane cleanup probes: fail
- production runtime queue integration: fail

The queue probe distinguishes emission and drain from backend-capable submit. Explicit backend_code=0 packets drain as typed UNAVAILABLE. BrowserBackend proves that a frame carries queue submit/drain metadata, a prepared Draw IR dispatch payload receipt, a positive backend handle from the Engine2D readback receipt, and a same-frame Engine2D pixel readback receipt, and resets all of them on cache hits.

## Run Environment

- root: /Users/ormastes/simple
- build_dir: build/production_gui_web_host_gpu_queue_readback_macos
- report_path: doc/09_report/production_gui_web_host_gpu_queue_readback_2026-07-10.md
- simple_bin: bin/simple
- simple_lib: src
- uname_s: Darwin
- uname_m: arm64
- child_timeout_seconds: 240
- probe_timeout_seconds: 180
- compiler_probe_timeout_seconds: 300

## Readback Matrix

| Backend | Child status | Production subcheck | Submit attempted | Readback available | Timed out | Timeout s | Reason | Report |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| vulkan | fail | fail | n/a | n/a | false | 240 | evidence-program-failed | build/production_gui_web_host_gpu_queue_readback_macos/vulkan/report.md |
| cuda | unavailable | host-unavailable | false | false | false | 240 | missing-verified-ptx | build/production_gui_web_host_gpu_queue_readback_macos/cuda/report.md |
| opencl | unavailable | unavailable | false | false | false | 240 | missing-opencl-runtime-loader | build/production_gui_web_host_gpu_queue_readback_macos/opencl/report.md |
| metal | pass | pass | true | true | false | 240 | gpu-readback-verified | build/production_gui_web_host_gpu_queue_readback_macos/metal/report.md |
| rocm | unavailable | host-unavailable | false | false | false | 240 | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback_macos/rocm/report.md |

## Presentation/Upload Provenance

| Backend | Provenance-only status | Evidence kind | Source | Exit code | Device readback proof |
| --- | --- | --- | --- | --- | --- |
| directx | provenance-only-pass | structured_readback_contract | structured_readback_contract | 0 | not_device_readback |
| webgpu | provenance-only-pass | provenance_only | surface_upload | 0 | not_device_readback |
| webgpu_real | unavailable | device_readback | not_device_readback | 1 | handle=0, checksum=-1, report=build/production_gui_web_host_gpu_queue_readback_macos/webgpu_real/report.md |
| directx_native | unavailable | native_device_readback | gate=unavailable, child_gate=unavailable, verdict=unavailable | 1/wrapper=1 | reason=directx-native-readback-requires-windows-win32-real, report=build/production_gui_web_host_gpu_queue_readback_macos/directx_native/report.md, child_report=build/production_gui_web_host_gpu_queue_readback_macos/directx_native/report.md |
| directx_native_spec | pass | sspec_wrapper_contract | test/03_system/check/directx_native_readback_spec.spl | 0 | wrapper contract evidence for native DirectX gate |
| generated_2d_native_wrappers_spec | pass | sspec_wrapper_contract | test/03_system/check/generated_2d_native_readback_wrappers_spec.spl | 0 | wrapper contract evidence for Metal/ROCm native readback gates |
| nogc_draw_ir_runtime_queue | pass | canonical_no_gc_queue_dispatch | test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl | 0 | required_for_Draw_IR_queue_dispatch |
| gc_draw_ir_runtime_queue | pass | legacy_gc_queue_bridge | test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl | 0 | compatibility bridge evidence |
| browser_event | fail | host_event_roundtrip | browser_backend_event_queue | 1 | required_for_host_event_roundtrip |
| event_queue | pass | runtime_event_receipt | runtime_event_receipt | 0 | required_for_event_flow |
| contract | pass | backend_handle_contract | backend_handle_contract | 0 | required_for_device_readback |
| metadata | pass | readback_metadata_predicate | device_readback/provenance_only | 0 | required_for_device_readback |

## Platform Spark / Normal-LLM Verification

| Platform | Spark task status | Normal-LLM verification | Expected proof | Current evidence |
| --- | --- | --- | --- | --- |
| linux_gui_web | fail | pass | same-frame Vulkan BrowserBackend device_readback plus event/queue correlation | event=browser-input-1; packet=1; source=device_readback; checksum=868306808 |
| metal | pass | pass | native Metal device readback on Darwin | Metal native readback evidence passed on Darwin. |
| rocm_hip | host-unavailable | host-unavailable | ROCm/HIP submit/readback on AMD ROCm host | ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host. |
| directx | structured-readback-contract | structured-readback-contract-pass-native-pending | same-frame DirectX device_readback | structured=structured_readback_contract/not_device_readback; native=unavailable/unavailable; gate=unavailable; child_gate=unavailable; reason=directx-native-readback-requires-windows-win32-real |
| webgpu | provenance-only | provenance-only-guard-pass | same-frame WebGPU device_readback | surface_upload/not_device_readback |

## Host Validation Commands
### Apple Metal (Darwin)
- Ensure Xcode command-line tools are available and active:
  - `xcode-select --install`
  - `xcode-select --print-path`
- Validate Metal toolchain/runtime visibility:
  - `xcrun --find metal`
  - `xcrun --find metallib`
  - `system_profiler SPDisplaysDataType`
- Rebuild generated toolchains:
  - `SIMPLE_BIN=${SIMPLE_BIN:-bin/simple} SIMPLE_LIB=${SIMPLE_LIB:-src} sh scripts/check/check-portable-compute-toolchains.shs`
- Run direct Metal proof:
  - `SIMPLE_BIN=${SIMPLE_BIN:-bin/simple} SIMPLE_LIB=${SIMPLE_LIB:-src} sh scripts/check/check-metal-generated-2d-readback.shs`
- Re-run platform aggregate:
  - `SIMPLE_BIN=${SIMPLE_BIN:-bin/simple} SIMPLE_LIB=${SIMPLE_LIB:-src} sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`

### AMD ROCm (Linux)
- Ensure ROCm/HIP tooling and runtime are available:
  - `hipcc --version`
  - `rocminfo`
- Verify AMD loader/runtime presence and target architecture.
- Rebuild generated toolchains:
  - `SIMPLE_BIN=${SIMPLE_BIN:-bin/simple} SIMPLE_LIB=${SIMPLE_LIB:-src} HIPCC_TOOL=${HIPCC_TOOL:-hipcc} HIP_ARCH=${HIP_ARCH:-gfx1100} sh scripts/check/check-portable-compute-toolchains.shs`
- Run direct ROCm/HIP proof:
  - `SIMPLE_BIN=${SIMPLE_BIN:-bin/simple} SIMPLE_LIB=${SIMPLE_LIB:-src} HIP_ARCH=${HIP_ARCH:-gfx1100} sh scripts/check/check-rocm-generated-2d-readback.shs`
- Re-run platform aggregate:
  - `SIMPLE_BIN=${SIMPLE_BIN:-bin/simple} SIMPLE_LIB=${SIMPLE_LIB:-src} sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`

## Production Gaps

- Rust/C capacity parity: pass (C capacity 1024, Rust 1024).
- Runtime queue overflow evidence: pass (accepted 1024/1024, overflow packet 0, drained 1024).
- SUBMITTED status usage: used (5 assignments observed outside constants).
- Runtime backend-handle field roundtrip: pass (synthetic probe handle 7; 49 matching runtime queue handle accessors/fields observed).
- Runtime payload metadata roundtrip: pass (payload_size 512, payload_hash 98765).
- Runtime payload text roundtrip: pass (queue probe payload command=draw_ir_rect id=runtime-backend).
- BrowserBackend host event roundtrip: fail (source browser_backend_event_queue, exit 1, reason browser-backend-event-ingress-contract-fail).
- BrowserBackend runtime queue handle/payload/perf: fail (backend vulkan, first_render_us 8431206, first_under_budget false, second_render_us 97, second_under_budget true, pixels 3072, checksum 858903428, nonuniform 3071, handle 7, packet 1, payload_size 12288, payload_hash 868306808, payload_text web-render-frame;backend=vulkan;pixels=3072;checksum=868306808, dispatch dispatched, dispatch_payload_size 512, dispatch_layout_commands 8, dispatch_payload_hash 941781836, dispatch_payload_text draw_ir schema=simple-draw-ir-v2, semantic rect/text/image 4/3/1, gui_ast true, widgets root/copy/action/image true/true/true/true, image_uri true, event_context true/browser-frame-16/gui_ast, cache reset not_requested/0).
- Same-frame GUI/web Engine2D pixel readback receipt: pass (backend vulkan, pixels 3072, checksum 868306808, reason same-frame Engine2D read_pixels, cache reset not_requested).
- Same-frame Vulkan/BrowserBackend device readback receipt: pass (source device_readback; only device_readback is accepted as device proof. BrowserBackend backend handle 7, same-frame checksum 868306808, Vulkan Engine2D child readback fail).
- Browser input event to queued frame/readback correlation: pass (status event_frame_readback_correlated, event browser-input-1, summary event=browser-input-1;frame_packet=1;readback_source=device_readback;checksum=868306808, cache reset not_requested).
- Runtime event receipt contract: pass (exit 0; drained backend handles must come from runtime receipt state).
- Backend readback handle contract: pass (exit 0; zero-handle device_readback must not masquerade as backend proof).
- Engine2D readback metadata proof predicate: pass (exit 0; device proof requires source device_readback, a positive backend handle, and nonempty pixels; DirectX structured readback remains native-pending, and surface_upload remains provenance_only).
- Compiler HostGpuLane cleanup probes: fail (hir-or-interpreter-cleanup-probe-failed; HIR exit 101, interpreter body-error exit 0).
- DirectX/WebGPU presentation provenance: DirectX pass source structured_readback_contract; DirectX native gate unavailable, child gate unavailable, wrapper exit 1; WebGPU upload pass source surface_upload; WebGPU real unavailable source not_device_readback, handle 0, expected/actual checksum 0/-1; provenance guard pass.
- Metal: Metal native readback evidence passed on Darwin.
- ROCm: ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.

## TODO Tracker

- Engine2DReadback carries source, backend_handle, pixel_count, checksum, and reason metadata; backend identity remains WebRender artifact metadata.
- Add Linux ROCm pass evidence when ROCm runtime, probe, device, and verified HSACO are present.
- Apple Metal pass evidence is present: native Metal generated-2D readback and the production wrapper Metal subcheck passed on Darwin.
- Add native DirectX device-readback evidence by making build/production_gui_web_host_gpu_queue_readback_macos/directx_native/report.md pass on Windows; current DirectX structured readback contract is handle/checksum-gated but remains native-pending and not production device_readback. WebGPU real device_readback evidence passes; surface_upload remains provenance-only.

## Raw Evidence

- run_root_dir=/Users/ormastes/simple
- run_build_dir=build/production_gui_web_host_gpu_queue_readback_macos
- run_report_path=doc/09_report/production_gui_web_host_gpu_queue_readback_2026-07-10.md
- run_simple_bin=bin/simple
- run_simple_lib=src
- run_uname_s=Darwin
- run_uname_m=arm64
- run_child_timeout_seconds=240
- run_probe_timeout_seconds=180
- run_compiler_probe_timeout_seconds=300
- queue_probe_source=test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl
- queue_probe_exit_code=0
- queue_probe_timeout_seconds=180
- queue_probe_timed_out=false
- queue_zero_backend_packet_id=1
- queue_zero_backend_queued_status=1
- queue_zero_backend_drained=1
- queue_zero_backend_last_status=4
- queue_zero_backend_last_backend_handle=0
- queue_nonzero_backend_packet_id=1
- queue_nonzero_backend_queued_status=1
- queue_nonzero_backend_drained=1
- queue_nonzero_backend_packet_count=1
- queue_nonzero_backend_submitted_count=1
- queue_nonzero_backend_completed_count=1
- queue_nonzero_backend_last_status=3
- queue_nonzero_backend_last_backend_handle=7
- queue_nonzero_backend_last_payload_size=512
- queue_nonzero_backend_last_payload_hash=98765
- queue_nonzero_backend_last_payload_text=queue probe payload command=draw_ir_rect id=runtime-backend
- queue_overflow_capacity=1024
- queue_overflow_accepted=1024
- queue_overflow_packet_id=0
- queue_overflow_packet_count=1024
- queue_overflow_drained=1024
- draw_ir_runtime_queue_spec_exit_code=0
- draw_ir_runtime_queue_spec_timeout_seconds=180
- draw_ir_runtime_queue_spec_timed_out=false
- nogc_draw_ir_runtime_queue_spec_exit_code=0
- nogc_draw_ir_runtime_queue_spec_timeout_seconds=180
- nogc_draw_ir_runtime_queue_spec_timed_out=false
- gc_draw_ir_runtime_queue_spec_exit_code=0
- gc_draw_ir_runtime_queue_spec_timeout_seconds=180
- gc_draw_ir_runtime_queue_spec_timed_out=false
- host_gpu_event_queue_spec_exit_code=0
- host_gpu_event_queue_spec_timeout_seconds=180
- host_gpu_event_queue_spec_timed_out=false
- browser_host_event_roundtrip_exit_code=1
- browser_host_event_roundtrip_timeout_seconds=180
- browser_host_event_roundtrip_timed_out=false
- draw_ir_runtime_queue_status=pass
- nogc_draw_ir_runtime_queue_status=pass
- gc_draw_ir_runtime_queue_status=pass
- host_gpu_event_queue_status=pass
- browser_host_event_roundtrip_status=fail
- browser_host_event_roundtrip_reason=browser-backend-event-ingress-contract-fail
- browser_host_event_roundtrip_source=browser_backend_event_queue
- directx_presentation_provenance_spec_exit_code=0
- directx_presentation_provenance_spec_timeout_seconds=180
- directx_presentation_provenance_spec_timed_out=false
- webgpu_upload_provenance_spec_exit_code=0
- webgpu_upload_provenance_spec_timeout_seconds=180
- webgpu_upload_provenance_spec_timed_out=false
- backend_readback_handle_contract_spec_exit_code=0
- backend_readback_handle_contract_spec_timeout_seconds=180
- backend_readback_handle_contract_spec_timed_out=false
- engine2d_readback_metadata_spec_exit_code=0
- engine2d_readback_metadata_spec_timeout_seconds=180
- engine2d_readback_metadata_spec_timed_out=false
- directx_presentation_provenance_status=pass
- webgpu_upload_provenance_status=pass
- backend_readback_handle_contract_status=pass
- engine2d_readback_metadata_status=pass
- directx_presentation_provenance_source=structured_readback_contract
- directx_structured_readback_contract_status=pass
- directx_structured_readback_contract_reason=backend spec proves positive readback handle plus checksum gate
- webgpu_upload_provenance_source=surface_upload
- directx_presentation_evidence_kind=structured_readback_contract
- webgpu_upload_evidence_kind=provenance_only
- presentation_provenance_device_readback_status=not_device_readback
- compiler_hir_host_gpu_lane_statement_tests_exit_code=101
- compiler_hir_host_gpu_lane_statement_tests_timeout_seconds=300
- compiler_hir_host_gpu_lane_statement_tests_timed_out=false
- compiler_host_gpu_lane_error_test_exit_code=0
- compiler_host_gpu_lane_error_test_timeout_seconds=300
- compiler_host_gpu_lane_error_test_timed_out=false
- compiler_host_gpu_lane_cleanup_status=fail
- compiler_host_gpu_lane_cleanup_reason=hir-or-interpreter-cleanup-probe-failed
- browser_frame_probe_exit_code=0
- browser_frame_probe_timeout_seconds=180
- browser_frame_probe_timed_out=false
- browser_backend=vulkan
- browser_first_render_us=8431206
- browser_first_render_under_budget=false
- browser_first_render_dom_layout_us=1160
- browser_first_render_html_us=68
- browser_first_render_pixel_artifact_us=8386437
- browser_first_render_draw_ir_dispatch_us=1871
- browser_first_render_framebuffer_copy_us=3689
- browser_first_render_state_store_us=30
- browser_first_pixel_count=3072
- browser_first_checksum=858903428
- browser_first_nonuniform_count=3071
- browser_first_submit=submitted
- browser_first_drain=drained
- browser_first_packet=1
- browser_first_drained=1
- browser_first_backend_handle=7
- browser_first_payload_size=12288
- browser_first_payload_hash=868306808
- browser_first_payload_text=web-render-frame;backend=vulkan;pixels=3072;checksum=868306808
- browser_first_dispatch_status=dispatched
- browser_first_dispatch_reason=Draw IR runtime packet dispatched to Engine2D backend
- browser_first_dispatch_payload_size=512
- browser_first_dispatch_layout_command_count=8
- browser_first_dispatch_payload_hash=941781836
- browser_first_dispatch_payload_text=draw_ir schema=simple-draw-ir-v2
- browser_first_dispatch_rect_command_count=4
- browser_first_dispatch_text_command_count=3
- browser_first_dispatch_image_command_count=1
- browser_first_dispatch_has_gui_ast_source=true
- browser_first_dispatch_has_root_widget=true
- browser_first_dispatch_has_copy_text=true
- browser_first_dispatch_has_action_text=true
- browser_first_dispatch_has_image_widget=true
- browser_first_dispatch_has_image_uri=true
- browser_first_dispatch_target_context_resolved=true
- browser_first_dispatch_target_context_batch_id=browser-frame-16
- browser_first_dispatch_target_context_surface_id=browser-frame
- browser_first_dispatch_target_context_component_id=browser-frame
- browser_first_dispatch_target_context_source_kind=gui_ast
- browser_first_reason=drained runtime queue
- browser_first_readback_status=readback
- browser_first_readback_backend=vulkan
- browser_first_readback_pixel_count=3072
- browser_first_readback_checksum=868306808
- browser_first_readback_reason=same-frame Engine2D read_pixels
- browser_first_gpu_readback_source=device_readback
- browser_first_event_correlation_status=event_frame_readback_correlated
- browser_first_event_correlation_id=browser-input-1
- browser_first_event_correlation_summary=event=browser-input-1;frame_packet=1;readback_source=device_readback;checksum=868306808
- browser_first_event_correlation_queue_packet=1
- browser_first_event_correlation_readback_source=device_readback
- browser_first_event_correlation_readback_checksum=868306808
- browser_event_roundtrip_status=rendered
- browser_event_enqueued_count=1
- browser_event_polled_count=1
- browser_event_dispatched_count=1
- browser_event_host_gpu_target_lane=gpu
- browser_event_host_gpu_forwarded=true
- browser_event_host_gpu_backward_completed=false
- browser_event_host_gpu_summary=event=browser-input-1;requested=gpu;decision=gpu;queued=true;gpu_batched=true;reason=
- browser_second_render_us=97
- browser_second_render_under_budget=true
- browser_second_fast_hits=1
- browser_second_submit=not_requested
- browser_second_drain=not_requested
- browser_second_packet=0
- browser_second_drained=0
- browser_second_backend_handle=0
- browser_second_payload_size=0
- browser_second_payload_hash=0
- browser_second_payload_text=
- browser_second_dispatch_status=not_requested
- browser_second_dispatch_reason=runtime dispatch not requested
- browser_second_dispatch_payload_size=0
- browser_second_dispatch_layout_command_count=0
- browser_second_dispatch_payload_hash=0
- browser_second_dispatch_payload_text=
- browser_second_dispatch_rect_command_count=0
- browser_second_dispatch_text_command_count=0
- browser_second_dispatch_image_command_count=0
- browser_second_dispatch_has_gui_ast_source=false
- browser_second_dispatch_has_root_widget=false
- browser_second_dispatch_has_copy_text=false
- browser_second_dispatch_has_action_text=false
- browser_second_dispatch_has_image_widget=false
- browser_second_dispatch_has_image_uri=false
- browser_second_dispatch_target_context_resolved=false
- browser_second_dispatch_target_context_batch_id=
- browser_second_dispatch_target_context_surface_id=
- browser_second_dispatch_target_context_component_id=
- browser_second_dispatch_target_context_source_kind=
- browser_second_reason=runtime queue not requested
- browser_second_readback_status=not_requested
- browser_second_readback_backend=
- browser_second_readback_pixel_count=0
- browser_second_readback_checksum=0
- browser_second_readback_reason=backend readback not requested
- browser_second_gpu_readback_source=not_requested
- browser_second_event_correlation_status=not_requested
- browser_second_event_correlation_id=
- browser_second_event_correlation_summary=
- browser_second_event_correlation_queue_packet=0
- browser_second_event_correlation_readback_source=not_requested
- browser_second_event_correlation_readback_checksum=0
- readback_vulkan_exit_code=1
- readback_vulkan_timeout_seconds=240
- readback_vulkan_timed_out=false
- readback_vulkan_status=fail
- readback_vulkan_reason=evidence-program-failed
- readback_vulkan_verdict=fail
- readback_vulkan_raw_evidence_status=fail
- readback_vulkan_report=build/production_gui_web_host_gpu_queue_readback_macos/vulkan/report.md
- readback_cuda_exit_code=0
- readback_cuda_timeout_seconds=240
- readback_cuda_timed_out=false
- readback_cuda_status=unavailable
- readback_cuda_reason=missing-verified-ptx
- readback_cuda_verdict=host-unavailable
- readback_cuda_raw_evidence_status=missing
- readback_cuda_report=build/production_gui_web_host_gpu_queue_readback_macos/cuda/report.md
- readback_cuda_submit_attempted=false
- readback_cuda_readback_available=false
- readback_opencl_exit_code=1
- readback_opencl_timeout_seconds=240
- readback_opencl_timed_out=false
- readback_opencl_status=unavailable
- readback_opencl_reason=missing-opencl-runtime-loader
- readback_opencl_verdict=unavailable
- readback_opencl_raw_evidence_status=missing
- readback_opencl_report=build/production_gui_web_host_gpu_queue_readback_macos/opencl/report.md
- readback_opencl_submit_attempted=false
- readback_opencl_readback_available=false
- readback_metal_exit_code=0
- readback_metal_timeout_seconds=240
- readback_metal_timed_out=false
- readback_metal_status=pass
- readback_metal_reason=gpu-readback-verified
- readback_metal_verdict=pass
- readback_metal_raw_evidence_status=missing
- readback_metal_report=build/production_gui_web_host_gpu_queue_readback_macos/metal/report.md
- readback_metal_submit_attempted=true
- readback_metal_readback_available=true
- readback_rocm_exit_code=1
- readback_rocm_timeout_seconds=240
- readback_rocm_timed_out=false
- readback_rocm_status=unavailable
- readback_rocm_reason=missing-primary-tool
- readback_rocm_verdict=host-unavailable
- readback_rocm_raw_evidence_status=missing
- readback_rocm_report=build/production_gui_web_host_gpu_queue_readback_macos/rocm/report.md
- readback_rocm_submit_attempted=false
- readback_rocm_readback_available=false
- readback_directx_native_exit_code=1
- readback_directx_native_timeout_seconds=240
- readback_directx_native_timed_out=false
- readback_directx_native_status=unavailable
- readback_directx_native_reason=directx-native-readback-requires-windows-win32-real
- readback_directx_native_verdict=unavailable
- readback_directx_native_raw_evidence_status=missing
- readback_directx_native_report=build/production_gui_web_host_gpu_queue_readback_macos/directx_native/report.md
- readback_directx_native_wrapper_gate_status=unavailable
- readback_directx_native_wrapper_exit_code=1
- readback_directx_native_child_report=build/production_gui_web_host_gpu_queue_readback_macos/directx_native/report.md
- directx_native_readback_spec_exit_code=0
- directx_native_readback_spec_timeout_seconds=180
- directx_native_readback_spec_timed_out=false
- generated_2d_native_readback_wrappers_spec_exit_code=0
- generated_2d_native_readback_wrappers_spec_timeout_seconds=180
- generated_2d_native_readback_wrappers_spec_timed_out=false
- directx_native_readback_spec_status=pass
- generated_2d_native_readback_wrappers_spec_status=pass
- native_readback_wrapper_sspec_coverage_status=pass
- native_readback_wrapper_sspec_doc_evidence_status=pass
- webgpu_real_readback_exit_code=1
- webgpu_real_readback_timeout_seconds=180
- webgpu_real_readback_timed_out=false
- webgpu_real_readback_status=unavailable
- webgpu_real_readback_reason=webgpu-real-probe-run-failed
- webgpu_real_readback_source=not_device_readback
- webgpu_real_readback_backend_handle=0
- webgpu_real_readback_expected_checksum=0
- webgpu_real_readback_actual_checksum=-1
- webgpu_real_readback_report=build/production_gui_web_host_gpu_queue_readback_macos/webgpu_real/report.md
- queue_c_capacity=1024
- queue_rust_capacity=1024
- queue_capacity_parity_status=pass
- queue_submitted_status_assignment_count=5
- queue_submitted_status_usage=used
- queue_concrete_backend_handle_field_count=49
- queue_backend_handle_roundtrip_status=pass
- queue_concrete_backend_handle_status=pass
- queue_emit_status=pass
- queue_zero_backend_status=unavailable
- queue_nonzero_backend_drain_status=pass
- queue_nonzero_backend_payload_status=pass
- queue_nonzero_backend_payload_text_status=pass
- presentation_provenance_guard_status=pass
- queue_overflow_status=pass
- browser_frame_queue_status=fail
- same_frame_backend_readback_status=pass
- same_frame_gpu_backend_readback_status=pass
- event_frame_correlation_status=pass
- production_runtime_queue_integration_status=fail
- production_runtime_queue_integration_reason=browser-frame-first-render-budget-not-met
- metal_host_availability=host-available
- metal_host_unavailable_reason=Metal native readback evidence passed on Darwin.
- rocm_host_availability=host-unavailable-or-runtime-missing
- rocm_host_unavailable_reason=ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.
- metal_spark_task_status=pass
- metal_normal_llm_verification_status=pass
- rocm_spark_task_status=host-unavailable
- rocm_normal_llm_verification_status=host-unavailable
- directx_spark_task_status=structured-readback-contract
- directx_normal_llm_verification_status=structured-readback-contract-pass-native-pending
- directx_native_gate_status=unavailable
- webgpu_spark_task_status=provenance-only
- webgpu_normal_llm_verification_status=provenance-only-guard-pass
- platform_matrix_status=partial
- full_host_gpu_platform_matrix_status=partial
- linux_gui_web_queue_integration_status=fail
- linux_gui_web_queue_integration_reason=browser-frame-first-render-budget-not-met
- joined_gui_web_device_readback_backend=vulkan
- missing_device_readback_platforms=rocm,directx,webgpu
- production_gui_web_host_gpu_queue_readback_status=fail
- production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met
