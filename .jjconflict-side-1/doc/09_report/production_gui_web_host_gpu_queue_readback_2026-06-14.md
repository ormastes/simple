# Production GUI/Web Host-GPU Queue Readback Evidence

Date: 2026-06-14

## Summary

- status: pass
- reason: same-frame BrowserBackend queue and GPU command-buffer readback receipt proven
- queue emission via rt_host_gpu_queue_emit: pass
- backend_code=0 drain result: unavailable
- nonzero backend-code drain result: pass
- queue overflow rejection: pass
- BrowserBackend frame queue bridge: pass
- same-frame BrowserBackend Engine2D pixel readback receipt: pass
- same-frame GPU command-buffer readback receipt: pass
- production runtime queue integration: pass

The queue probe distinguishes emission and drain from backend-capable submit. Interpreter or fallback GPU packets with backend_code=0 drain as typed UNAVAILABLE. BrowserBackend proves that a frame carries queue submit/drain metadata, a same-frame Engine2D read_pixels receipt, and resets both on cache hits.

## Readback Matrix

| Backend | Child status | Production subcheck | Reason | Report |
| --- | --- | --- | --- | --- |
| vulkan | pass | pass | pass | build/production_gui_web_host_gpu_queue_readback_sync/vulkan/report.md |
| cuda | pass | pass | readback-pixels-matched | build/production_gui_web_host_gpu_queue_readback_sync/cuda/report.md |
| metal | unavailable | host-unavailable | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback_sync/metal/report.md |
| rocm | unavailable | host-unavailable | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback_sync/rocm/report.md |

## Production Gaps

- Rust/C capacity parity: pass (C capacity missing, Rust missing).
- Runtime queue overflow evidence: pass (accepted missing/1024, overflow packet 0, drained 1024).
- SUBMITTED status usage: used (5 assignments observed outside constants).
- Runtime backend-handle field roundtrip: pass (synthetic probe handle 7; 38 matching runtime queue handle accessors/fields observed).
- BrowserBackend runtime queue handle: pass (backend vulkan, pixels 3072, checksum 772887022, nonuniform 2884, handle 7, packet 1, cache reset not_requested).
- Same-frame GUI/web Engine2D pixel readback receipt: pass (backend vulkan, pixels 3072, checksum 782290402, cache reset not_requested).
- Same-frame GPU command-buffer readback receipt: pass (source device_readback; only device_readback is accepted as command-buffer proof. BrowserBackend Vulkan handle 7, same-frame checksum 782290402, Vulkan Engine2D child readback pass).
- Metal: Metal requires Apple platform runtime; this host is Linux.
- ROCm: ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.

## TODO Tracker

- Extend Engine2DReadback with backend, pixel count, checksum, and reason metadata if richer provenance reports are needed.
- Add Linux ROCm pass evidence when ROCm runtime, probe, device, and verified HSACO are present.
- Add Apple Metal pass evidence on an Apple host.

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
- queue_overflow_capacity=1024
- queue_overflow_accepted=1024
- queue_overflow_packet_id=0
- queue_overflow_packet_count=1024
- queue_overflow_drained=1024
- draw_ir_runtime_queue_spec_exit_code=0
- browser_frame_probe_exit_code=0
- browser_backend=vulkan
- browser_first_pixel_count=3072
- browser_first_checksum=772887022
- browser_first_nonuniform_count=2884
- browser_first_submit=submitted
- browser_first_drain=drained
- browser_first_packet=1
- browser_first_drained=1
- browser_first_backend_handle=7
- browser_first_reason=drained runtime queue
- browser_first_readback_status=readback
- browser_first_readback_backend=vulkan
- browser_first_readback_pixel_count=3072
- browser_first_readback_checksum=782290402
- browser_first_readback_reason=same-frame Engine2D read_pixels
- browser_first_gpu_readback_source=device_readback
- browser_second_fast_hits=1
- browser_second_submit=not_requested
- browser_second_drain=not_requested
- browser_second_packet=0
- browser_second_drained=0
- browser_second_backend_handle=0
- browser_second_reason=runtime queue not requested
- browser_second_readback_status=not_requested
- browser_second_readback_backend=
- browser_second_readback_pixel_count=0
- browser_second_readback_checksum=0
- browser_second_readback_reason=backend readback not requested
- browser_second_gpu_readback_source=not_requested
- readback_vulkan_exit_code=0
- readback_vulkan_status=pass
- readback_vulkan_reason=pass
- readback_vulkan_verdict=pass
- readback_vulkan_report=build/production_gui_web_host_gpu_queue_readback_sync/vulkan/report.md
- readback_cuda_exit_code=0
- readback_cuda_status=pass
- readback_cuda_reason=readback-pixels-matched
- readback_cuda_verdict=pass
- readback_cuda_report=build/production_gui_web_host_gpu_queue_readback_sync/cuda/report.md
- readback_metal_exit_code=1
- readback_metal_status=unavailable
- readback_metal_reason=missing-primary-tool
- readback_metal_verdict=host-unavailable
- readback_metal_report=build/production_gui_web_host_gpu_queue_readback_sync/metal/report.md
- readback_rocm_exit_code=1
- readback_rocm_status=unavailable
- readback_rocm_reason=missing-primary-tool
- readback_rocm_verdict=host-unavailable
- readback_rocm_report=build/production_gui_web_host_gpu_queue_readback_sync/rocm/report.md
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
- queue_overflow_status=pass
- browser_frame_queue_status=pass
- same_frame_backend_readback_status=pass
- same_frame_gpu_backend_readback_status=pass
- production_runtime_queue_integration_status=pass
- production_runtime_queue_integration_reason=same-frame BrowserBackend queue and GPU command-buffer readback receipt proven
- metal_host_availability=host-unavailable-linux
- metal_host_unavailable_reason=Metal requires Apple platform runtime; this host is Linux.
- rocm_host_availability=host-unavailable-or-runtime-missing
- rocm_host_unavailable_reason=ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.
- production_gui_web_host_gpu_queue_readback_status=pass
- production_gui_web_host_gpu_queue_readback_reason=same-frame BrowserBackend queue and GPU command-buffer readback receipt proven
