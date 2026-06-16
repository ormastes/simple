# Production GUI/Web Host-GPU Queue Readback Evidence

Date: 2026-06-16

## Summary

- linux GUI/web queue integration status: fail
- linux GUI/web queue integration reason: browser-frame-first-render-budget-not-met
- legacy compatibility status key: production_gui_web_host_gpu_queue_readback_status=fail
- legacy compatibility reason key: production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met
- full host-GPU platform matrix status: partial
- joined GUI/web device readback backend: 
- missing device-readback platforms: metal,rocm,directx,webgpu
- queue emission via rt_host_gpu_queue_emit: pass
- backend_code=0 drain result: unavailable
- nonzero backend-code drain result: pass
- nonzero backend-code payload receipt: pass
- nonzero backend-code payload text receipt: pass
- DirectX/WebGPU provenance guard: fail
- DirectX native gate: fail
- native readback wrapper SSpec coverage: pass
- native readback wrapper generated-doc evidence: pass
- queue overflow rejection: pass
- BrowserBackend frame queue bridge: fail
- BrowserBackend host event roundtrip: fail
- same-frame BrowserBackend Engine2D pixel readback receipt: fail
- same-frame Vulkan/BrowserBackend device readback receipt: missing
- browser input event to queued frame/readback correlation: fail
- runtime event receipt contract: fail
- backend readback handle contract: fail
- Engine2D readback metadata proof predicate: fail
- compiler HostGpuLane cleanup probes: fail
- production runtime queue integration: fail

The queue probe distinguishes emission and drain from backend-capable submit. Explicit backend_code=0 packets drain as typed UNAVAILABLE. BrowserBackend proves that a frame carries queue submit/drain metadata, a prepared Draw IR dispatch payload receipt, a positive backend handle from the Engine2D readback receipt, and a same-frame Engine2D pixel readback receipt, and resets all of them on cache hits.

## Run Environment

- root: /home/ormastes/dev/pub/simple
- build_dir: build/production_gui_web_host_gpu_queue_readback
- report_path: doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md
- simple_bin: ./bin/simple
- simple_lib: src
- uname_s: Linux
- uname_m: x86_64
- child_timeout_seconds: 240
- probe_timeout_seconds: 180
- compiler_probe_timeout_seconds: 300

## Readback Matrix

| Backend | Child status | Production subcheck | Submit attempted | Readback available | Timed out | Timeout s | Reason | Report |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| vulkan | pass | pass | n/a | n/a | false | 240 | pass | build/production_gui_web_host_gpu_queue_readback/vulkan/report.md |
| cuda | pass | pass | true | true | false | 240 | readback-pixels-matched | build/production_gui_web_host_gpu_queue_readback/cuda/report.md |
| opencl | pass | pass | true | true | false | 240 | readback-pixels-matched | build/production_gui_web_host_gpu_queue_readback/opencl/report.md |
| metal | unavailable | host-unavailable | false | false | false | 240 | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback/metal/report.md |
| rocm | unavailable | host-unavailable | false | false | false | 240 | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback/rocm/report.md |

## Presentation/Upload Provenance

| Backend | Provenance-only status | Evidence kind | Source | Exit code | Device readback proof |
| --- | --- | --- | --- | --- | --- |
| directx | fail | structured_readback_contract | swapchain_present | 1 | not_device_readback |
| webgpu | provenance-only-pass | provenance_only | surface_upload | 0 | not_device_readback |
| webgpu_real | unavailable | device_readback | not_device_readback | 1 | handle=0, checksum=-1, report=build/production_gui_web_host_gpu_queue_readback/webgpu_real/report.md |
| directx_native | unavailable | native_device_readback | gate=fail, child_gate=unavailable, verdict=unavailable | 1/wrapper=1 | reason=directx-native-readback-requires-windows-win32-real, report=build/production_gui_web_host_gpu_queue_readback/directx_native/report.md, child_report=build/production_gui_web_host_gpu_queue_readback/directx_native/report.md |
| directx_native_spec | pass | sspec_wrapper_contract | test/03_system/check/directx_native_readback_spec.spl | 0 | wrapper contract evidence for native DirectX gate |
| generated_2d_native_wrappers_spec | pass | sspec_wrapper_contract | test/03_system/check/generated_2d_native_readback_wrappers_spec.spl | 0 | wrapper contract evidence for Metal/ROCm native readback gates |
| nogc_draw_ir_runtime_queue | fail | canonical_no_gc_queue_dispatch | test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl | 1 | required_for_Draw_IR_queue_dispatch |
| gc_draw_ir_runtime_queue | fail | legacy_gc_queue_bridge | test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl | 1 | compatibility bridge evidence |
| browser_event | fail | host_event_roundtrip | browser_backend_event_queue | 1 | required_for_host_event_roundtrip |
| event_queue | fail | runtime_event_receipt | runtime_event_receipt | 1 | required_for_event_flow |
| contract | fail | backend_handle_contract | backend_handle_contract | 1 | required_for_device_readback |
| metadata | fail | readback_metadata_predicate | device_readback/provenance_only | 1 | required_for_device_readback |

## Platform Spark / Normal-LLM Verification

| Platform | Spark task status | Normal-LLM verification | Expected proof | Current evidence |
| --- | --- | --- | --- | --- |
| linux_gui_web | fail | fail | same-frame Vulkan BrowserBackend device_readback plus event/queue correlation | event=missing; packet=missing; source=missing; checksum=missing |
| metal | host-unavailable | host-unavailable | native Metal device readback on Darwin | Metal requires Apple platform runtime; this host is Linux. |
| rocm_hip | host-unavailable | host-unavailable | ROCm/HIP submit/readback on AMD ROCm host | ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host. |
| directx | fail | fail | same-frame DirectX device_readback | structured=swapchain_present/not_device_readback; native=unavailable/unavailable; gate=fail; child_gate=unavailable; reason=directx-native-readback-requires-windows-win32-real |
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
- Runtime backend-handle field roundtrip: pass (synthetic probe handle 7; 38 matching runtime queue handle accessors/fields observed).
- Runtime payload metadata roundtrip: pass (payload_size 512, payload_hash 98765).
- Runtime payload text roundtrip: pass (queue probe payload command=draw_ir_rect id=runtime-backend).
- BrowserBackend host event roundtrip: fail (source browser_backend_event_queue, exit 1, reason browser-backend-event-ingress-contract-fail).
- BrowserBackend runtime queue handle/payload/perf: fail (backend missing, first_render_us missing, first_under_budget missing, second_render_us missing, second_under_budget missing, pixels missing, checksum missing, nonuniform missing, handle missing, packet missing, payload_size missing, payload_hash missing, payload_text missing, dispatch missing, dispatch_payload_size missing, dispatch_layout_commands missing, dispatch_payload_hash missing, dispatch_payload_text missing, semantic rect/text/image missing/missing/missing, gui_ast missing, widgets root/copy/action/image missing/missing/missing/missing, image_uri missing, event_context missing/missing/missing, cache reset missing/missing).
- Same-frame GUI/web Engine2D pixel readback receipt: fail (backend missing, pixels missing, checksum missing, reason missing, cache reset missing).
- Same-frame Vulkan/BrowserBackend device readback receipt: missing (source missing; only device_readback is accepted as device proof. BrowserBackend backend handle missing, same-frame checksum missing, Vulkan Engine2D child readback pass).
- Browser input event to queued frame/readback correlation: fail (status missing, event missing, summary missing, cache reset missing).
- Runtime event receipt contract: fail (exit 1; drained backend handles must come from runtime receipt state).
- Backend readback handle contract: fail (exit 1; zero-handle device_readback must not masquerade as backend proof).
- Engine2D readback metadata proof predicate: fail (exit 1; device proof requires source device_readback, a positive backend handle, and nonempty pixels; DirectX structured readback remains native-pending, and surface_upload remains provenance_only).
- Compiler HostGpuLane cleanup probes: fail (hir-or-interpreter-cleanup-probe-failed; HIR exit 101, interpreter body-error exit 0).
- DirectX/WebGPU presentation provenance: DirectX fail source swapchain_present; DirectX native gate fail, child gate unavailable, wrapper exit 1; WebGPU upload pass source surface_upload; WebGPU real unavailable source not_device_readback, handle 0, expected/actual checksum 0/-1; provenance guard fail.
- Metal: Metal requires Apple platform runtime; this host is Linux.
- ROCm: ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.

## TODO Tracker

- Engine2DReadback carries source, backend_handle, pixel_count, checksum, and reason metadata; backend identity remains WebRender artifact metadata.
- Add Linux ROCm pass evidence when ROCm runtime, probe, device, and verified HSACO are present.
- Add Apple Metal pass evidence on an Apple host.
- Add native DirectX device-readback evidence by making build/production_gui_web_host_gpu_queue_readback/directx_native/report.md pass on Windows; current DirectX structured readback contract is handle/checksum-gated but remains native-pending and not production device_readback. WebGPU real device_readback evidence passes; surface_upload remains provenance-only.

## Raw Evidence

- run_root_dir=/home/ormastes/dev/pub/simple
- run_build_dir=build/production_gui_web_host_gpu_queue_readback
- run_report_path=doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md
- run_simple_bin=./bin/simple
- run_simple_lib=src
- run_uname_s=Linux
- run_uname_m=x86_64
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
- draw_ir_runtime_queue_spec_exit_code=1
- draw_ir_runtime_queue_spec_timeout_seconds=180
- draw_ir_runtime_queue_spec_timed_out=false
- nogc_draw_ir_runtime_queue_spec_exit_code=1
- nogc_draw_ir_runtime_queue_spec_timeout_seconds=180
- nogc_draw_ir_runtime_queue_spec_timed_out=false
- gc_draw_ir_runtime_queue_spec_exit_code=1
- gc_draw_ir_runtime_queue_spec_timeout_seconds=180
- gc_draw_ir_runtime_queue_spec_timed_out=false
- host_gpu_event_queue_spec_exit_code=1
- host_gpu_event_queue_spec_timeout_seconds=180
- host_gpu_event_queue_spec_timed_out=false
- browser_host_event_roundtrip_exit_code=1
- browser_host_event_roundtrip_timeout_seconds=180
- browser_host_event_roundtrip_timed_out=false
- draw_ir_runtime_queue_status=fail
- nogc_draw_ir_runtime_queue_status=fail
- gc_draw_ir_runtime_queue_status=fail
- host_gpu_event_queue_status=fail
- browser_host_event_roundtrip_status=fail
- browser_host_event_roundtrip_reason=browser-backend-event-ingress-contract-fail
- browser_host_event_roundtrip_source=browser_backend_event_queue
- directx_presentation_provenance_spec_exit_code=1
- directx_presentation_provenance_spec_timeout_seconds=180
- directx_presentation_provenance_spec_timed_out=false
- webgpu_upload_provenance_spec_exit_code=0
- webgpu_upload_provenance_spec_timeout_seconds=180
- webgpu_upload_provenance_spec_timed_out=false
- backend_readback_handle_contract_spec_exit_code=1
- backend_readback_handle_contract_spec_timeout_seconds=180
- backend_readback_handle_contract_spec_timed_out=false
- engine2d_readback_metadata_spec_exit_code=1
- engine2d_readback_metadata_spec_timeout_seconds=180
- engine2d_readback_metadata_spec_timed_out=false
- directx_presentation_provenance_status=fail
- webgpu_upload_provenance_status=pass
- backend_readback_handle_contract_status=fail
- engine2d_readback_metadata_status=fail
- directx_presentation_provenance_source=swapchain_present
- directx_structured_readback_contract_status=fail
- directx_structured_readback_contract_reason=backend spec failed
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
- browser_frame_probe_exit_code=1
- browser_frame_probe_timeout_seconds=180
- browser_frame_probe_timed_out=false
- browser_backend=
- browser_first_render_us=
- browser_first_render_under_budget=
- browser_first_render_dom_layout_us=
- browser_first_render_html_us=
- browser_first_render_pixel_artifact_us=
- browser_first_render_draw_ir_dispatch_us=
- browser_first_render_framebuffer_copy_us=
- browser_first_render_state_store_us=
- browser_first_pixel_count=
- browser_first_checksum=
- browser_first_nonuniform_count=
- browser_first_submit=
- browser_first_drain=
- browser_first_packet=
- browser_first_drained=
- browser_first_backend_handle=
- browser_first_payload_size=
- browser_first_payload_hash=
- browser_first_payload_text=
- browser_first_dispatch_status=
- browser_first_dispatch_reason=
- browser_first_dispatch_payload_size=
- browser_first_dispatch_layout_command_count=
- browser_first_dispatch_payload_hash=
- browser_first_dispatch_payload_text=
- browser_first_dispatch_rect_command_count=
- browser_first_dispatch_text_command_count=
- browser_first_dispatch_image_command_count=
- browser_first_dispatch_has_gui_ast_source=
- browser_first_dispatch_has_root_widget=
- browser_first_dispatch_has_copy_text=
- browser_first_dispatch_has_action_text=
- browser_first_dispatch_has_image_widget=
- browser_first_dispatch_has_image_uri=
- browser_first_dispatch_target_context_resolved=
- browser_first_dispatch_target_context_batch_id=
- browser_first_dispatch_target_context_surface_id=
- browser_first_dispatch_target_context_component_id=
- browser_first_dispatch_target_context_source_kind=
- browser_first_reason=
- browser_first_readback_status=
- browser_first_readback_backend=
- browser_first_readback_pixel_count=
- browser_first_readback_checksum=
- browser_first_readback_reason=
- browser_first_gpu_readback_source=
- browser_first_event_correlation_status=
- browser_first_event_correlation_id=
- browser_first_event_correlation_summary=
- browser_first_event_correlation_queue_packet=
- browser_first_event_correlation_readback_source=
- browser_first_event_correlation_readback_checksum=
- browser_event_roundtrip_status=
- browser_event_enqueued_count=
- browser_event_polled_count=
- browser_event_dispatched_count=
- browser_event_host_gpu_target_lane=
- browser_event_host_gpu_forwarded=
- browser_event_host_gpu_backward_completed=
- browser_event_host_gpu_summary=
- browser_second_render_us=
- browser_second_render_under_budget=
- browser_second_fast_hits=
- browser_second_submit=
- browser_second_drain=
- browser_second_packet=
- browser_second_drained=
- browser_second_backend_handle=
- browser_second_payload_size=
- browser_second_payload_hash=
- browser_second_payload_text=
- browser_second_dispatch_status=
- browser_second_dispatch_reason=
- browser_second_dispatch_payload_size=
- browser_second_dispatch_layout_command_count=
- browser_second_dispatch_payload_hash=
- browser_second_dispatch_payload_text=
- browser_second_dispatch_rect_command_count=
- browser_second_dispatch_text_command_count=
- browser_second_dispatch_image_command_count=
- browser_second_dispatch_has_gui_ast_source=
- browser_second_dispatch_has_root_widget=
- browser_second_dispatch_has_copy_text=
- browser_second_dispatch_has_action_text=
- browser_second_dispatch_has_image_widget=
- browser_second_dispatch_has_image_uri=
- browser_second_dispatch_target_context_resolved=
- browser_second_dispatch_target_context_batch_id=
- browser_second_dispatch_target_context_surface_id=
- browser_second_dispatch_target_context_component_id=
- browser_second_dispatch_target_context_source_kind=
- browser_second_reason=
- browser_second_readback_status=
- browser_second_readback_backend=
- browser_second_readback_pixel_count=
- browser_second_readback_checksum=
- browser_second_readback_reason=
- browser_second_gpu_readback_source=
- browser_second_event_correlation_status=
- browser_second_event_correlation_id=
- browser_second_event_correlation_summary=
- browser_second_event_correlation_queue_packet=
- browser_second_event_correlation_readback_source=
- browser_second_event_correlation_readback_checksum=
- readback_vulkan_exit_code=0
- readback_vulkan_timeout_seconds=240
- readback_vulkan_timed_out=false
- readback_vulkan_status=pass
- readback_vulkan_reason=pass
- readback_vulkan_verdict=pass
- readback_vulkan_report=build/production_gui_web_host_gpu_queue_readback/vulkan/report.md
- readback_cuda_exit_code=0
- readback_cuda_timeout_seconds=240
- readback_cuda_timed_out=false
- readback_cuda_status=pass
- readback_cuda_reason=readback-pixels-matched
- readback_cuda_verdict=pass
- readback_cuda_report=build/production_gui_web_host_gpu_queue_readback/cuda/report.md
- readback_cuda_submit_attempted=true
- readback_cuda_readback_available=true
- readback_opencl_exit_code=0
- readback_opencl_timeout_seconds=240
- readback_opencl_timed_out=false
- readback_opencl_status=pass
- readback_opencl_reason=readback-pixels-matched
- readback_opencl_verdict=pass
- readback_opencl_report=build/production_gui_web_host_gpu_queue_readback/opencl/report.md
- readback_opencl_submit_attempted=true
- readback_opencl_readback_available=true
- readback_metal_exit_code=1
- readback_metal_timeout_seconds=240
- readback_metal_timed_out=false
- readback_metal_status=unavailable
- readback_metal_reason=missing-primary-tool
- readback_metal_verdict=host-unavailable
- readback_metal_report=build/production_gui_web_host_gpu_queue_readback/metal/report.md
- readback_metal_submit_attempted=false
- readback_metal_readback_available=false
- readback_rocm_exit_code=1
- readback_rocm_timeout_seconds=240
- readback_rocm_timed_out=false
- readback_rocm_status=unavailable
- readback_rocm_reason=missing-primary-tool
- readback_rocm_verdict=host-unavailable
- readback_rocm_report=build/production_gui_web_host_gpu_queue_readback/rocm/report.md
- readback_rocm_submit_attempted=false
- readback_rocm_readback_available=false
- readback_directx_native_exit_code=1
- readback_directx_native_timeout_seconds=240
- readback_directx_native_timed_out=false
- readback_directx_native_status=unavailable
- readback_directx_native_reason=directx-native-readback-requires-windows-win32-real
- readback_directx_native_verdict=unavailable
- readback_directx_native_report=build/production_gui_web_host_gpu_queue_readback/directx_native/report.md
- readback_directx_native_wrapper_gate_status=unavailable
- readback_directx_native_wrapper_exit_code=1
- readback_directx_native_child_report=build/production_gui_web_host_gpu_queue_readback/directx_native/report.md
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
- webgpu_real_readback_report=build/production_gui_web_host_gpu_queue_readback/webgpu_real/report.md
- queue_c_capacity=1024
- queue_rust_capacity=1024
- queue_capacity_parity_status=pass
- queue_submitted_status_assignment_count=5
- queue_submitted_status_usage=used
- queue_concrete_backend_handle_field_count=38
- queue_backend_handle_roundtrip_status=pass
- queue_concrete_backend_handle_status=pass
- queue_emit_status=pass
- queue_zero_backend_status=unavailable
- queue_nonzero_backend_drain_status=pass
- queue_nonzero_backend_payload_status=pass
- queue_nonzero_backend_payload_text_status=pass
- presentation_provenance_guard_status=fail
- queue_overflow_status=pass
- browser_frame_queue_status=fail
- same_frame_backend_readback_status=fail
- same_frame_gpu_backend_readback_status=missing
- event_frame_correlation_status=fail
- production_runtime_queue_integration_status=fail
- production_runtime_queue_integration_reason=browser-frame-first-render-budget-not-met
- metal_host_availability=host-unavailable-Linux
- metal_host_unavailable_reason=Metal requires Apple platform runtime; this host is Linux.
- rocm_host_availability=host-unavailable-or-runtime-missing
- rocm_host_unavailable_reason=ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.
- metal_spark_task_status=host-unavailable
- metal_normal_llm_verification_status=host-unavailable
- rocm_spark_task_status=host-unavailable
- rocm_normal_llm_verification_status=host-unavailable
- directx_spark_task_status=fail
- directx_normal_llm_verification_status=fail
- directx_native_gate_status=fail
- webgpu_spark_task_status=provenance-only
- webgpu_normal_llm_verification_status=provenance-only-guard-pass
- platform_matrix_status=partial
- full_host_gpu_platform_matrix_status=partial
- linux_gui_web_queue_integration_status=fail
- linux_gui_web_queue_integration_reason=browser-frame-first-render-budget-not-met
- joined_gui_web_device_readback_backend=
- missing_device_readback_platforms=metal,rocm,directx,webgpu
- production_gui_web_host_gpu_queue_readback_status=fail
- production_gui_web_host_gpu_queue_readback_reason=browser-frame-first-render-budget-not-met
