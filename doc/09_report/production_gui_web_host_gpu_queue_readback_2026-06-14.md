# Production GUI/Web Host-GPU Queue Readback Evidence

Date: 2026-06-14

## Summary

- status: fail
- reason: backend-runtime-queue-integration-not-proven
- queue emission via rt_host_gpu_queue_emit: pass
- backend_code=0 drain result: unavailable
- nonzero backend-code drain result: pass
- production runtime queue integration: fail

The queue probe distinguishes emission and drain from backend-capable submit. Interpreter or fallback GPU packets with backend_code=0 drain as typed UNAVAILABLE and are not counted as backend runtime integration. A nonzero backend code drains as COMPLETED, but this wrapper does not treat that as production-ready Vulkan/CUDA queue integration because no concrete backend runtime handle is carried in the queue packet.

## Readback Matrix

| Backend | Child status | Production subcheck | Reason | Report |
| --- | --- | --- | --- | --- |
| vulkan | pass | pass | pass | build/production_gui_web_host_gpu_queue_readback/vulkan/report.md |
| cuda | pass | pass | readback-pixels-matched | build/production_gui_web_host_gpu_queue_readback/cuda/report.md |
| metal | unavailable | host-unavailable | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback/metal/report.md |
| rocm | unavailable | host-unavailable | missing-primary-tool | build/production_gui_web_host_gpu_queue_readback/rocm/report.md |

## Production Gaps

- Rust/C capacity parity: gap (C capacity 1024, Rust missing).
- SUBMITTED status usage: unused (0 assignments observed outside constants).
- Concrete runtime backend handle carried through queue packet: missing (0 matching runtime queue fields observed).
- Metal: Metal requires Apple platform runtime; this host is Linux.
- ROCm: ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.

## TODO Tracker

- Attach a concrete Vulkan/CUDA backend runtime handle to queue packets instead of only backend_code.
- Align Rust and C queue capacity behavior and add overflow evidence.
- Either use RT_HOST_GPU_QUEUE_STATUS_SUBMITTED during drain or remove it from the public status contract.
- Add Linux ROCm pass evidence when ROCm runtime, probe, device, and verified HSACO are present.

## Raw Evidence

- queue_probe_exit_code=0
- queue_zero_backend_packet_id=1
- queue_zero_backend_queued_status=1
- queue_zero_backend_drained=1
- queue_zero_backend_last_status=4
- queue_nonzero_backend_packet_id=1
- queue_nonzero_backend_queued_status=1
- queue_nonzero_backend_drained=1
- queue_nonzero_backend_packet_count=1
- queue_nonzero_backend_submitted_count=1
- queue_nonzero_backend_completed_count=1
- queue_nonzero_backend_last_status=3
- draw_ir_runtime_queue_spec_exit_code=0
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
- queue_rust_capacity=missing
- queue_capacity_parity_status=gap
- queue_submitted_status_assignment_count=0
- queue_submitted_status_usage=unused
- queue_concrete_backend_handle_field_count=0
- queue_concrete_backend_handle_status=missing
- queue_emit_status=pass
- queue_zero_backend_status=unavailable
- queue_nonzero_backend_drain_status=pass
- production_runtime_queue_integration_status=fail
- production_runtime_queue_integration_reason=nonzero-backend-code-drains-completed-but-no-concrete-vulkan-or-cuda-runtime-handle-is-carried-through-queue-packet
- metal_host_availability=host-unavailable-linux
- metal_host_unavailable_reason=Metal requires Apple platform runtime; this host is Linux.
- rocm_host_availability=host-unavailable-or-runtime-missing
- rocm_host_unavailable_reason=ROCm requires AMD ROCm runtime, device, probe tool, and verified HSACO on host.
- production_gui_web_host_gpu_queue_readback_status=fail
- production_gui_web_host_gpu_queue_readback_reason=backend-runtime-queue-integration-not-proven
