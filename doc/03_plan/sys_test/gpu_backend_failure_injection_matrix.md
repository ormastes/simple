# GPU Backend Failure-Injection Matrix

This matrix covers the canonical SimpleOS host-GPU protocol owner at
`src/lib/common/gpu/simpleos_host_gpu_protocol.spl` and the host executor at
`src/app/simpleos_gpu_host/main.spl`. The companion system spec injects
structured `SimpleOsHostGpuBatch` and `SimpleOsHostGpuReceipt` values into the
real batch and receipt checkers. It does not claim a live GPU fault run.

## Receipt Rules

| Fault | Expected status | Fallback | Required receipt fields |
|---|---|---|---|
| Backend unavailable | `unsupported` | None for a strict requested GPU | `backend=unavailable`, non-empty reason, zero native handle, no device readback |
| Invalid request | `fail` | None | Correlated generation/run/frame, `reason=invalid-request`, no native handle |
| Submit failure | `fail` | None unless policy explicitly opts in | Requested backend remains identifiable; non-empty submit-failure reason; no pass receipt |
| Readback mismatch | `fail` | None unless policy explicitly opts in | `reason=checksum-mismatch`; no device-backed pass; mismatched output is rejected |
| Explicit CPU fallback | `fallback` | CPU only when explicitly allowed | `backend=cpu`, `readback_source=cpu_reference`, `native_handle=0`, non-empty reason |

Wire reason `16` identifies backend submit/dispatch failure and reason `17`
identifies backend readback failure. Checksum mismatch retains reason `11`.
Every `fail`, `unsupported`, or `blocked` receipt must have zero handle,
identity, output bytes, and checksum with `readback_source=none`.

A requested CUDA/Vulkan/Metal batch must never receive `status=pass` with
`backend=cpu`, `readback_source=cpu_reference`, or a missing native handle.
The positive native handle field is a non-owning execution-provenance token;
it must not expose a buffer or device resource after executor cleanup.
The requested backend is `batch.backend`; the actual backend is
`receipt.backend`. A fallback is therefore visible rather than silently
reported as accelerated execution.

## Injection Status

`implemented` means the named production branch already emits a non-pass
result, or the companion spec already injects and validates the receipt.
`checker-only` means the spec constructs a receipt at the validator boundary;
it is not a live backend fault. `TODO` means a deterministic backend seam is
still required before an end-to-end fault run can be claimed.

The production receipt is written by `_finish` in
`src/app/simpleos_gpu_host/main.spl`. The checker receipt is constructed by
`receipt(...)` in
`test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl`.
The executor-level companion
`gpu_backend_failure_injection_spec.spl` also exercises the guarded
`SIMPLE_GPU_TEST=1` and `SIMPLE_GPU_FAULT_INJECT=<backend>:<phase>` seam.
CUDA init/submit/readback/mismatch passes live. Vulkan is implemented but the
current runtime artifact lacks `rt_vulkan_dependency_quarantine_lock`; the
same tests remain skipped until that artifact is incrementally rebuilt.

## Backend Injection Matrix

Each row names the exact current branch, the receipt contract, and the
assertion that must fail closed. The same receipt contract applies to all
three processing backends; backend-specific points are kept explicit so a
future adapter hook cannot silently cover only one implementation.

### CUDA

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | `processing_ir_execute_cuda`: guarded `unavailable` phase before runtime probing; host admission is `_processing_backend_mask_supported` | `unsupported`; `backend=unavailable`; `reason=backend-unavailable`; `native_handle=0`; `readback_source=none`; zero output fields | No `status=pass` receipt may have CPU backend/readback | Guarded live control implemented; HELLO removes the unavailable backend |
| Init/submit | Init: `cuda_device_get`, `cuda_ctx_create`, or `cuda_module_load_data`; submit: `cuda_launch_kernel`/`cuda_sync` | `fail`; requested backend remains `cuda`; wire reason `16` for submit/dispatch; handle `0`; no device readback | Assert failed status, exact reason code, handle `0`, and no device readback | Guarded init/submit seams and real `cuda-dispatch-failed` split implemented |
| Readback | `cuda_memcpy_dtoh` in `copied`, followed by host value extraction | `fail`; wire reason `17`; handle `0`; `readback_source=none`; zero output | Reject any pass lacking positive provenance, identity, exact output size/checksum, and `device_readback` | Guarded readback seam and real `cuda-readback-failed` split implemented |
| Mismatch | Host `processing_ir_outputs_equal(values, oracle)` in `_process_request`; checker `mismatch` receipt constructor | `fail`; `backend=cuda`; wire reason `11`; handle `0`; no device-backed pass | Assert mismatch is non-pass and reject forged pass output | Guarded mismatch seam, production comparison, and wire mapping implemented |
| Explicit fallback | No CUDA runtime fallback in `_process_request`; checker `receipt(..., "fallback", "cpu", ..., "cpu_reference", 0, ...)` | `fallback`; `backend=cpu`; `reason` non-empty; `native_handle=0`; `readback_source=cpu_reference`; correlated generation/run/frame | Accept only explicit `fallback`; reject same fields with `status=pass`, and reject fallback with nonzero handle or device readback | Checker-only `implemented`; live policy-controlled fallback hook `TODO` |

### Vulkan

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | Guarded `unavailable` phase before `vulkan_init`; render admission also reaches `_create_render_backend` `Err` | `unsupported`; `backend=unavailable`; handle `0`; no device readback | Do not promote an unavailable request to pass or silently rewrite `batch.backend` | Guarded live control implemented |
| Init/submit | Init: `vulkan_alloc_storage`, `vulkan_compile_spirv`, `vulkan_create_pipeline_with_push`; submit: `vulkan_sffi_dispatch_buffer_compute_checked` | `fail`; `backend=vulkan`; wire reason `16` for submit/dispatch; handle `0`; no device readback | Assert no positive provenance/identity, no device readback, and no pass status | Guarded seams implemented; live completion waits for updated runtime artifact |
| Readback | `vulkan_sffi_read_buffer_bytes` and `bytes.len() == byte_count`; render path `engine.read_pixels_with_source` | `fail`; wire reason `17`; handle `0`; no output checksum | Reject short/empty bytes and every pass whose source is not device readback | Guarded seam implemented; live completion waits for updated runtime artifact |
| Mismatch | Processing `processing_ir_outputs_equal(values, oracle)`; Draw IR canonical checksum check before render | `fail`; wire reason `11`; handle `0`; no device-backed pass | Assert mismatch is non-pass and forged output is rejected | Guarded seam and wire mapping implemented; live completion waits for updated runtime artifact |
| Explicit fallback | No automatic Vulkan-to-CPU path in the SimpleOS host; checker fallback constructor only | `fallback`; `backend=cpu`; `reason` non-empty; handle `0`; `readback_source=cpu_reference` | Reject `pass/cpu/cpu_reference`; accept fallback only when policy explicitly requests it and correlation fields match | Checker-only `implemented`; live policy hook `TODO` |

### Metal

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | Guarded `unavailable` phase before Metal availability/init; render creation is the platform Engine2D owner | `unsupported`; `backend=unavailable`; handle `0`; no device readback | Linux/unavailable output is not a Metal pass; reject any pass without Metal provenance, identity, and device readback | Guarded seam implemented; prepared-macOS live run pending |
| Init/submit | Init: `metal_sffi_create_device`, queue, shader, pipeline, or allocation; submit: `metal_sffi_run_compute_frame` | `fail`; `backend=metal`; non-empty init/submit reason; handle `0`; no device readback | Accept only as failed; assert no pass, positive provenance, or device readback is emitted after the injected error | Guarded init/submit seams implemented; prepared-macOS live run pending |
| Readback | `metal_buffer_download_ptr` and `values.len() == element_count`; render `read_pixels_with_source` | `fail`; `reason=readback-failed` or `readback-size-mismatch`; handle `0`; zero output | Reject short readback, absent checksum, absent identity, or any source other than `device_readback` | Guarded readback seam implemented after successful dispatch; prepared-macOS live run pending |
| Mismatch | Host `processing_ir_outputs_equal(values, oracle)` / Draw IR canonical checksum; synthetic checker `mismatch` receipt | `fail`; `backend=metal`; `reason=checksum-mismatch`; handle `0`; no device-backed pass | Assert failed status and exact reason; reject CPU masquerading and altered output checksum | Guarded mismatch seam implemented after valid readback size; prepared-macOS live run pending |
| Explicit fallback | No automatic Metal-to-CPU path in the SimpleOS host; checker fallback constructor | `fallback`; `backend=cpu`; `reason` non-empty; handle `0`; `readback_source=cpu_reference` | Reject `status=pass` with CPU provenance; fallback is valid only with explicit policy and correlated IDs | Checker-only `implemented`; live policy hook `TODO`, macOS |

Metal rows above are deliberately not closed by Linux interpreter or
unavailability output. Live init/submit/readback/mismatch/fallback execution
must run on the prepared macOS host and record native device identity,
submit/readback markers, and exact mismatch fields.

The executable checker for the matrix is:

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl \
  --mode=interpreter
```

## Linux Ownership

Linux owns the host daemon, Vulkan Engine2D, and CUDA ProcessingIR rows. Run
the existing backend evidence gates with the repository's current compiler:

```sh
SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-vulkan-engine2d-readback.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-cuda-generated-2d-readback.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

For the SimpleOS ivshmem host path, the existing Linux/QEMU owner is:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

These commands prove available-backend execution and canonical readback. They
do not inject submit or readback faults.

## macOS Ownership

macOS owns the live Metal rows and the macOS Vulkan/Metal parity rows. Run
these only on a macOS host with the required Xcode/Vulkan tools:

```sh
SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-metal-generated-2d-readback.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Until a macOS host runs these, Metal live status is postponed; Linux
unavailability is not a Metal pass.

### Prepared macOS ProcessingIR Resume

- Prerequisites: current pure-Simple runtime with Metal SFFI, an available
  Metal device, Xcode command-line tools, and `SIMPLE_LIB=src`.
- Command:
  `mkdir -p build/simpleos_gpu_host && SIMPLE_LIB=src bin/simple test test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl --mode=interpreter > build/simpleos_gpu_host/gpu_backend_failure_injection_macos.log 2>&1`.
- Retain:
  `build/simpleos_gpu_host/gpu_backend_failure_injection_macos.log`.
- Owner: prepared macOS host operator.
- Final reviewer: high-capability model comparing all five Metal phase results
  with the disabled-default case and zero failure handles/identities.

## Open Hooks

The following are the exact remaining implementation gaps. They are not
covered by the checker-level spec and must not be marked complete from
synthetic receipts:

1. Add a live explicit-fallback policy input to the host only after the
   requested GPU failure is observed; never infer fallback from a missing
   handle. The fallback receipt must carry `cpu_reference`, zero handle, and
   a non-empty reason.
2. Add end-to-end daemon tests that assert the wire fields at
   `SIMPLEOS_HOST_GPU_WIRE_STATUS`, `...REASON`, `...NATIVE_HANDLE`,
   `...OUTPUT_BYTES`, `...OUTPUT_CHECKSUM`, `...READBACK_SOURCE`, and
   `...DEVICE_IDENTITY`, plus generation/run/frame correlation.
3. Run Metal live rows only on prepared macOS. Linux may run the validator and
   synthetic receipt cases, but cannot close Metal runtime evidence.
