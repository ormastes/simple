# Production GUI/Web Host-GPU Queue Readback System Test Plan

## Scope

Prove the production GUI/web host-GPU path with fail-closed evidence:

- `rt_host_gpu_queue_emit` records queue packets.
- `rt_host_gpu_queue_emit_payload` carries payload size/hash metadata through runtime drain receipt state.
- `rt_host_gpu_queue_emit_payload_text` carries bounded payload text through runtime drain receipt state.
- `rt_host_gpu_queue_drain` distinguishes backend-code `0` unavailable packets from nonzero backend-code packets.
- Vulkan, CUDA, and OpenCL readback wrappers pass where available.
- Metal and ROCm are reported as host-unavailable or runtime-unavailable with concrete reasons on Linux.

## Acceptance Criteria

- Queue emission is not treated as backend-capable submit by itself.
- `backend_code=0` drains as typed unavailable and cannot produce a production PASS.
- A nonzero backend-code drain may pass only the queue emit/drain subcheck; it is not evidence of backend-handle integration.
- A nonzero backend-code payload drain must report `queue_nonzero_backend_last_payload_size=512`, `queue_nonzero_backend_last_payload_hash=98765`, and `queue_nonzero_backend_last_payload_text=queue probe payload command=draw_ir_rect id=runtime-backend` in the wrapper raw evidence.
- On this Linux production lane, Vulkan, CUDA, and OpenCL child readback wrappers must report PASS; other hosts may record typed unavailable/runtime-unavailable child reasons only when the platform matrix explicitly marks that backend host-specific.
- Child backend verdicts must come from each wrapper's final backend-specific
  status key; a generic early `evidence_status=pass` is diagnostic only and
  cannot override a later focused-spec or readback failure.
- Metal and ROCm are recorded as host-unavailable on this Linux lane unless their required host runtime and tools are present.
- Backend runtime queue integration may PASS when the joined BrowserBackend frame proves queue submit/drain metadata, a positive `browser_first_backend_handle` propagated from the Engine2D backend readback receipt, frame payload metadata/text (`browser_first_payload_size=12288`, positive `browser_first_payload_hash`, and `browser_first_payload_text=web-render-frame;backend=vulkan;pixels=3072;checksum=...`), `browser_first_readback_pixel_count`, `browser_first_readback_checksum`, `browser_first_readback_reason`, and same-frame backend device readback source `device_readback`. Synthetic runtime-queue handles remain isolated probe evidence.
- `browser_host_event_roundtrip_status` must be `pass` so BrowserBackend host event ingress/dispatch/render telemetry is proven separately from frame readback.
- `host_gpu_event_queue_spec.spl` must PASS so GPU event submits require a positive backend handle and backward drain receipts come from runtime queue state.
- `draw_ir_runtime_queue_spec.spl` must PASS through the canonical no-GC
  `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` owner so
  Draw IR queue dispatch, payload receipts, and GC compatibility shims do not
  duplicate queue logic.
- `backend_readback_handle_contract_spec.spl` must PASS so zero-handle or fallback readbacks cannot masquerade as same-frame backend device proof.
- The report calls out Rust/C capacity parity and `SUBMITTED` status contract gaps when they remain present.
- The report publishes machine-readable platform handoff status fields for
  Spark/normal-LLM verification:
  `metal_spark_task_status`, `metal_normal_llm_verification_status`,
  `rocm_spark_task_status`, `rocm_normal_llm_verification_status`,
  `directx_spark_task_status`, `directx_normal_llm_verification_status`,
  `webgpu_spark_task_status`, and `webgpu_normal_llm_verification_status`.
  On Linux without Metal/ROCm hosts those platforms remain typed
  host-unavailable. DirectX is a structured readback contract with native
  Windows D3D11 proof pending; WebGPU real same-frame `device_readback` proof
  passes while WebGPU `surface_upload` remains provenance-only.
- The wrapper exits nonzero until queue emit/drain, payload metadata/text drain receipt, BrowserBackend host event roundtrip, BrowserBackend frame evidence, the runtime event receipt contract, the backend readback handle contract, same-frame backend device readback, DirectX structured-readback/native-pending guard, WebGPU real-readback/provenance guard, and available Vulkan/CUDA/OpenCL child readback wrappers all pass.

## Evidence Command

```bash
SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

The command is fail-closed for missing joined evidence. On this Linux lane, the accepted production pass requires BrowserBackend host event roundtrip telemetry plus a positive BrowserBackend backend handle, typed frame payload receipt, typed Engine2D readback metadata (`pixel_count`, `checksum`, and `reason`), and same-frame `device_readback`; cache-hit frames must reset the handle and payload fields to `0`/empty with `not_requested` queue/readback status. The BrowserBackend probe also gates conservative in-process frame timing (`first_render_under_budget=true`, `second_render_under_budget=true`) so startup cost cannot hide frame-path regressions. The runtime event receipt and backend readback handle contract specs are part of this gate.
Use `SIMPLE_BIN=src/compiler_rust/target/release/simple` or another freshly built driver when the local deployed `bin/simple` is stale or under investigation; the wrapper and child specs must still execute in separate processes and record the configured binary in the run environment.
The report/raw evidence must include `run_root_dir`, `run_build_dir`,
`run_report_path`, `run_simple_bin`, `run_simple_lib`, `run_uname_s`, and
`run_uname_m`, and backend child wrappers must receive the configured
`SIMPLE_BIN`/`SIMPLE_LIB` instead of silently falling back to another driver.
The wrapper must bound risky child work internally using `CHILD_TIMEOUT` for
backend readback wrappers and `PROBE_TIMEOUT` for `bin/simple` probes/tests, and
must publish `run_child_timeout_seconds` and `run_probe_timeout_seconds`.
Each backend child wrapper row must also publish
`readback_<backend>_timeout_seconds` and `readback_<backend>_timed_out`, so a
normal verifier can distinguish a backend failure from a bounded timeout.
`metal_host_availability` and `rocm_host_availability` must be derived from the
actual child readback verdict and recorded host identity, not hardcoded to the
Linux unavailable state when a platform child check passes on its required host.

## Platform Evidence Plan

- Linux Vulkan/CUDA/OpenCL: required local production evidence on this lane; all three must pass for the wrapper to return production PASS.
- macOS Metal: run the same wrapper on Darwin with `xcrun metal`, `xcrun metallib`, and native raw Metal readback evidence. Linux `host-unavailable` is not a Metal pass.
- ROCm/HIP: run on an AMD ROCm host with `hipcc`, loader libraries, device visibility, and verified HSACO for `HIP_ARCH`; Linux hosts without that stack remain typed unavailable.
- Windows DirectX: do not claim production readiness from DXVK setup alone. Run and promote the existing `scripts/check/check-directx-native-readback.shs` wrapper on a Windows `win32-real` host only when it returns `device_readback`, a positive backend handle, and matching checksums.
- WebGPU: real `device_readback` evidence now passes through `scripts/check/check-webgpu-real-readback.shs`; that gate requires pass status, `device_readback` provenance, a positive backend handle, and positive matching checksums. The separate WebGPU `surface_upload` provenance remains useful but is still not a device-readback proof.

The wrapper records DirectX structured/native-gate status and WebGPU `surface_upload`
focused spec results as presentation/upload provenance. These fields are useful
for platform planning, but they are explicitly reported as `not_device_readback`
and do not satisfy the production pass gate.
The wrapper also fails if those DirectX/WebGPU provenance fields are relabeled
as `device_readback` without a real backend readback receipt.
The WebGPU readback wrapper's `--self-test` rejects zero or malformed handles,
zero checksums, checksum mismatches, and upload-only provenance.
