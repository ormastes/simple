# Production GUI/Web Host-GPU Queue Readback Evidence

Date: 2026-06-16

## Summary

- linux GUI/web queue integration status: pass
- linux GUI/web queue integration reason: same-frame BrowserBackend queue, Draw IR dispatch, Vulkan/BrowserBackend device readback receipt, Engine2D readback proof predicate, and compiler HostGpuLane cleanup probes proven
- legacy compatibility status key: production_gui_web_host_gpu_queue_readback_status=pass
- legacy compatibility reason key: production_gui_web_host_gpu_queue_readback_reason=same-frame BrowserBackend queue, Draw IR dispatch, Vulkan/BrowserBackend device readback receipt, Engine2D readback proof predicate, and compiler HostGpuLane cleanup probes proven
- full host-GPU platform matrix status: partial
- joined GUI/web device readback backend: vulkan
- missing device-readback platforms: metal,rocm,directx,webgpu
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
- BrowserBackend frame queue bridge: pass
- BrowserBackend host event roundtrip: pass
- same-frame BrowserBackend Engine2D pixel readback receipt: pass
- same-frame Vulkan/BrowserBackend device readback receipt: pass
- browser input event to queued frame/readback correlation: pass
- runtime event receipt contract: pass
- backend readback handle contract: pass
- Engine2D readback metadata proof predicate: pass
- compiler HostGpuLane cleanup probes: pass
- production runtime queue integration: pass

The queue probe distinguishes emission and drain from backend-capable submit.
Explicit `backend_code=0` packets drain as typed `UNAVAILABLE`. BrowserBackend
proves that a frame carries queue submit/drain metadata, a prepared Draw IR
dispatch payload receipt, a positive backend handle from the Engine2D readback
receipt, and a same-frame Engine2D pixel readback receipt, and resets all of
them on cache hits.

## Run Environment

- root: repo checkout
- build_dir: build/production_gui_web_host_gpu_queue_readback
- report_path: doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md
- simple_bin: bin/simple
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

## Platform Status

- directx_native_gate_status=unavailable
- webgpu_spark_task_status=provenance-only
- webgpu_normal_llm_verification_status=provenance-only-guard-pass
- platform_matrix_status=partial
- full_host_gpu_platform_matrix_status=partial
- linux_gui_web_queue_integration_status=pass
- joined_gui_web_device_readback_backend=vulkan
- missing_device_readback_platforms=metal,rocm,directx,webgpu
- production_gui_web_host_gpu_queue_readback_status=pass
