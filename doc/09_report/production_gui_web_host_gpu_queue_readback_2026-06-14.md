# Production GUI/Web Host-GPU Queue Readback Evidence

Date: 2026-06-14

## Summary

- status: fail
- reason: same-frame-gui-web-backend-readback-receipt-not-proven
- queue emission via rt_host_gpu_queue_emit: pass
- backend_code=0 drain result: unavailable
- nonzero backend-code drain result: pass
- BrowserBackend frame queue bridge: pass
- production runtime queue integration: fail

The queue probe distinguishes emission and drain from backend-capable submit. Interpreter or fallback GPU packets with backend_code=0 drain as typed UNAVAILABLE. BrowserBackend must also prove that a real rendered frame carries queue submit/drain metadata and resets it on cache hits. Independent backend readback still remains a separate evidence layer until the same GUI/web frame produces a backend readback receipt.

## Readback Matrix

| Backend | Child status | Production subcheck | Reason | Report |
| --- | --- | --- | --- | --- |
| vulkan | pass | pass | pass | build/production_gui_web_host_gpu_queue_readback/vulkan/report.md |
| cuda | pass | pass | readback-pixels-matched | build/production_gui_web_host_gpu_queue_readback/cuda/report.md |
| metal | unavailable | host-unavailable | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback/metal/report.md |
| rocm | unavailable | host-unavailable | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback/rocm/report.md |

## Production Gaps

- Rust/C capacity parity: pass (C capacity 1024, Rust 1024).
- SUBMITTED status usage: used (5 assignments observed outside constants).
- Runtime backend-handle field roundtrip: pass (synthetic probe handle 7; 38 matching runtime queue handle accessors/fields observed).
- BrowserBackend runtime queue handle: pass (backend vulkan, handle 7, packet 1, cache reset not_requested).
- Same-frame GUI/web backend readback receipt: missing (Vulkan/CUDA readback is proven independently, not yet tied to this BrowserBackend frame).
- Metal: Metal requires Apple platform runtime; this host is Linux.
- ROCm: ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.

## TODO Tracker

- Fuse BrowserBackend frame runtime queue receipts with a same-frame Vulkan/CUDA backend readback receipt.
- Align Rust and C queue capacity behavior and add overflow evidence.
- Either use RT_HOST_GPU_QUEUE_STATUS_SUBMITTED during drain or remove it from the public status contract.
- Add Linux ROCm pass evidence when ROCm runtime, probe, device, and verified HSACO are present.

## Raw Evidence

- queue_probe_exit_code=0
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
- draw_ir_runtime_queue_spec_exit_code=0
- browser_frame_probe_exit_code=0
- browser_backend=vulkan
- browser_first_submit=submitted
- browser_first_drain=drained
- browser_first_packet=1
- browser_first_drained=1
- browser_first_backend_handle=7
- browser_first_reason=drained runtime queue
- browser_second_fast_hits=1
- browser_second_submit=not_requested
- browser_second_drain=not_requested
- browser_second_packet=0
- browser_second_drained=0
- browser_second_backend_handle=0
- browser_second_reason=runtime queue not requested
- readback_vulkan_exit_code=0
- readback_vulkan_status=pass
- readback_vulkan_reason=pass
- readback_vulkan_verdict=pass
- readback_vulkan_report=build/production_gui_web_host_gpu_queue_readback/vulkan/report.md
- readback_cuda_exit_code=0
- readback_cuda_status=pass
- readback_cuda_reason=readback-pixels-matched
- readback_cuda_verdict=pass
- readback_cuda_report=build/production_gui_web_host_gpu_queue_readback/cuda/report.md
- readback_metal_exit_code=1
- readback_metal_status=unavailable
- readback_metal_reason=missing-primary-tool
- readback_metal_verdict=host-unavailable
- readback_metal_report=build/production_gui_web_host_gpu_queue_readback/metal/report.md
- readback_rocm_exit_code=1
- readback_rocm_status=unavailable
- readback_rocm_reason=missing-primary-tool
- readback_rocm_verdict=host-unavailable
- readback_rocm_report=build/production_gui_web_host_gpu_queue_readback/rocm/report.md
- queue_c_capacity=1024
- queue_rust_capacity=1024
- queue_capacity_parity_status=pass
- queue_submitted_status_assignment_count=5
- queue_submitted_status_usage=used
- queue_concrete_backend_handle_field_count=38
- queue_backend_handle_roundtrip_status=pass
- queue_concrete_backend_handle_status=missing
- queue_emit_status=pass
- queue_zero_backend_status=unavailable
- queue_nonzero_backend_drain_status=pass
- browser_frame_queue_status=pass
- production_runtime_queue_integration_status=fail
- production_runtime_queue_integration_reason=browser-frame-runtime-queue-handle-present-but-same-frame-backend-readback-receipt-is-not-yet-fused
- metal_host_availability=host-unavailable-linux
- metal_host_unavailable_reason=Metal requires Apple platform runtime; this host is Linux.
- rocm_host_availability=host-unavailable-or-runtime-missing
- rocm_host_unavailable_reason=ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.
- production_gui_web_host_gpu_queue_readback_status=fail
- production_gui_web_host_gpu_queue_readback_reason=same-frame-gui-web-backend-readback-receipt-not-proven
