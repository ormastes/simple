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

A requested CUDA/Vulkan/Metal batch must never receive `status=pass` with
`backend=cpu`, `readback_source=cpu_reference`, or a missing native handle.
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
The latter is the only current way to inject `submit-failed` and a synthetic
readback mismatch without changing source or hardware state.

## Backend Injection Matrix

Each row names the exact current branch, the receipt contract, and the
assertion that must fail closed. The same receipt contract applies to all
three processing backends; backend-specific points are kept explicit so a
future adapter hook cannot silently cover only one implementation.

### CUDA

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | `processing_ir_execute_cuda`: `cuda_available`, `cuda_init`, or `cuda_device_count` false/zero; host admission is `_processing_backend_mask_supported` | `unsupported`; `backend=unavailable`; `reason=backend-unavailable`; `native_handle=0`; `readback_source=none`; zero output fields | `validate_receipt(...).status == "pass"` only for the validator acceptance of the `unsupported` receipt, and no `status=pass` receipt may have CPU backend/readback | `implemented` branch; `checker-only` injection; `TODO` live control hook |
| Init/submit | Init: `cuda_device_get`, `cuda_ctx_create`, or `cuda_module_load_data`; submit: `cuda_launch_kernel`/`cuda_sync` | `fail`; requested backend remains `cuda`; non-empty `reason` (`cuda-init-failed`, `cuda-context-create-failed`, `cuda-module-load-failed`, or `submit-failed`); handle `0`; no device readback | `validate_receipt(...).status == "pass"` for a failed receipt, then assert `status == "fail"`, `reason` non-empty, handle `0`, and `readback_source != "device_readback"` | Init branches `implemented`; submit reason is collapsed with readback; `checker-only` submit injection; `TODO` separate live submit hook |
| Readback | `cuda_memcpy_dtoh` in `copied`, followed by host value extraction | `fail`; `reason=readback-failed` (canonicalize the current `cuda-dispatch-or-readback-failed`); handle `0`; `readback_source=none`; zero output | Reject any pass lacking positive handle, identity, exact output size/checksum, and `device_readback` | `implemented` failure branch; `TODO` deterministic readback-only hook and reason split |
| Mismatch | Host `processing_ir_outputs_equal(values, oracle)` in `_process_request`; checker `mismatch` receipt constructor | `fail`; `backend=cuda`; `reason=checksum-mismatch`; handle `0`; no device-backed pass | `validate_receipt(...).status == "pass"`, then assert failed status/reason and reject a forged `pass` with CPU or mismatched output | Production comparison `implemented`; live provider corruption hook `TODO`; checker injection `implemented` |
| Explicit fallback | No CUDA runtime fallback in `_process_request`; checker `receipt(..., "fallback", "cpu", ..., "cpu_reference", 0, ...)` | `fallback`; `backend=cpu`; `reason` non-empty; `native_handle=0`; `readback_source=cpu_reference`; correlated generation/run/frame | Accept only explicit `fallback`; reject same fields with `status=pass`, and reject fallback with nonzero handle or device readback | Checker-only `implemented`; live policy-controlled fallback hook `TODO` |

### Vulkan

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | `processing_ir_execute_vulkan`: `vulkan_init` false or dependency quarantine not reaped; render admission also reaches `_create_render_backend` `Err` | `unsupported`; `backend=unavailable`; `reason=backend-unavailable`; handle `0`; `readback_source=none`; zero output | Do not promote an unavailable request to pass or silently rewrite `batch.backend`; explicit CPU fallback must use `status=fallback` | `implemented` branches; `checker-only` injection; `TODO` live control hook |
| Init/submit | Init: `vulkan_alloc_storage`, `vulkan_compile_spirv`, `vulkan_create_pipeline_with_push`; submit: `vulkan_sffi_dispatch_buffer_compute_checked` | `fail`; `backend=vulkan`; non-empty init/submit reason; handle `0`; no device readback | Failed receipt is accepted only as a failed receipt; assert no positive handle/identity, no `device_readback`, and no pass status | Init branches `implemented`; dispatch branch `implemented` but maps negative/zero to backend-specific reasons; `checker-only` submit injection; `TODO` deterministic seam |
| Readback | `vulkan_sffi_read_buffer_bytes` and `bytes.len() == byte_count`; render path `engine.read_pixels_with_source` | `fail`; `reason=readback-failed` or `non-device-readback`; handle `0`; no output checksum | Reject short/empty bytes and every pass whose source is not `device_readback` or whose output size/checksum is absent | `implemented` branch; `TODO` readback-only injection and stable reason |
| Mismatch | Processing `processing_ir_outputs_equal(values, oracle)`; Draw IR canonical checksum check before render | `fail`; `backend=vulkan`; `reason=checksum-mismatch`; handle `0`; no device-backed pass | Assert mismatch is non-pass and a forged pass with altered checksum/output is rejected | Comparison/checker injection `implemented`; live provider corruption hook `TODO` |
| Explicit fallback | No automatic Vulkan-to-CPU path in the SimpleOS host; checker fallback constructor only | `fallback`; `backend=cpu`; `reason` non-empty; handle `0`; `readback_source=cpu_reference` | Reject `pass/cpu/cpu_reference`; accept fallback only when policy explicitly requests it and correlation fields match | Checker-only `implemented`; live policy hook `TODO` |

### Metal

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | `processing_ir_execute_metal`: `metal_sffi_is_available`, `metal_sffi_init`, or `metal_sffi_device_count`; render creation is the platform Engine2D owner | `unsupported`; `backend=unavailable`; `reason=backend-unavailable`; handle `0`; `readback_source=none`; zero output | Linux/unavailable output is not a Metal pass; reject any pass without Metal handle, identity, and device readback | `implemented` branches; `checker-only` injection; live runtime `TODO`, postponed to prepared macOS |
| Init/submit | Init: `metal_sffi_create_device`, queue, shader, pipeline, or allocation; submit: `metal_sffi_run_compute_frame` | `fail`; `backend=metal`; non-empty init/submit reason; handle `0`; no device readback | Accept only as failed; assert no pass, positive provenance, or device readback is emitted after the injected error | Init branches `implemented`; submit failure is present but not externally injectable; `checker-only` submit injection; `TODO` live hook, macOS |
| Readback | `metal_buffer_download_ptr` and `values.len() == element_count`; render `read_pixels_with_source` | `fail`; `reason=readback-failed` or `readback-size-mismatch`; handle `0`; zero output | Reject short readback, absent checksum, absent identity, or any source other than `device_readback` | `implemented` branches; `TODO` deterministic readback-only hook, macOS |
| Mismatch | Host `processing_ir_outputs_equal(values, oracle)` / Draw IR canonical checksum; synthetic checker `mismatch` receipt | `fail`; `backend=metal`; `reason=checksum-mismatch`; handle `0`; no device-backed pass | Assert failed status and exact reason; reject CPU masquerading and altered output checksum | Comparison/checker injection `implemented`; live provider corruption hook `TODO`, macOS |
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

## Open Hooks

The following are the exact remaining implementation gaps. They are not
covered by the checker-level spec and must not be marked complete from
synthetic receipts:

1. Add one test-only, disabled-by-default adapter seam (environment or
   injected provider) for `unavailable`, `init`, `submit`, `readback`, and
   `mismatch`, with the same names for CUDA, Vulkan, and Metal. Do not add
   backend-specific production policy to the protocol.
2. Preserve the failure phase in the result/receipt. In particular, split
   CUDA `cuda-dispatch-or-readback-failed` and Metal
   `metal-readback-failed`/`metal-dispatch-failed` at the injection boundary,
   and map host `_finish` fields deterministically.
3. Add a live explicit-fallback policy input to the host only after the
   requested GPU failure is observed; never infer fallback from a missing
   handle. The fallback receipt must carry `cpu_reference`, zero handle, and
   a non-empty reason.
4. Add end-to-end daemon tests that assert the wire fields at
   `SIMPLEOS_HOST_GPU_WIRE_STATUS`, `...REASON`, `...NATIVE_HANDLE`,
   `...OUTPUT_BYTES`, `...OUTPUT_CHECKSUM`, `...READBACK_SOURCE`, and
   `...DEVICE_IDENTITY`, plus generation/run/frame correlation.
5. Run Metal live rows only on prepared macOS. Linux may run the validator and
   synthetic receipt cases, but cannot close Metal runtime evidence.
