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
The host defaults to `--processing-fallback=none`. Explicit
`--processing-fallback=cpu` computes and writes the CPU oracle only after a GPU
executor failure, output mismatch, or calibrated below-threshold decision. On the numeric wire this is
`status=4`, `readback_source=2`, zero native handle/identity, and the original
GPU failure reason. The completion backend remains the requested GPU code for
request correlation.

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
CUDA init/submit/readback/mismatch passes live. The source-matched Simple native
Vulkan probe now passes real device output plus unavailable, init, submit,
readback, and mismatch phases. The retained runtime archive exports both
`rt_vulkan_dependency_quarantine_lock` and `rt_is_interpreter_runtime`.

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
| Readback | `cuda_memcpy_dtoh` in `copied`, followed by host value extraction | `fail`; wire reason `17`; handle `0`; `readback_source=none`; zero output | Reject any pass lacking positive provenance, identity, exact output size/checksum, and `device_readback` | Same-process native baseline/readback-failure/recovery passes with exact 64-value output, zero failure provenance, and unchanged positive identity |
| Mismatch | Host `processing_ir_output_matches(ir, values)` in `_process_request`; checker `mismatch` receipt constructor | `fail`; `backend=cuda`; wire reason `11`; handle `0`; no device-backed pass | Assert mismatch is non-pass and reject forged pass output | Guarded mismatch seam, production comparison, and wire mapping implemented |
| Explicit fallback | `_process_request` calls `_processing_cpu_fallback` after executor failure or mismatch only when `--processing-fallback=cpu`; checker also covers the textual receipt | `fallback`; CPU readback; original GPU reason; zero native handle/identity; correlated generation/run/frame/backend | Accept only explicit `fallback`; reject the same fields with `status=pass`, nonzero provenance, device readback, or wrong correlation | Policy and guest wire validator implemented; end-to-end daemon wire run pending |

### Vulkan

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | Guarded `unavailable` phase before `vulkan_init`; render admission also reaches `_create_render_backend` `Err` | `unsupported`; `backend=unavailable`; handle `0`; no device readback | Do not promote an unavailable request to pass or silently rewrite `batch.backend` | Source-matched native phase passes with exact reason and zero provenance |
| Init/submit | Init: `vulkan_alloc_storage`, `vulkan_compile_spirv`, `vulkan_create_pipeline_with_push`; submit: `vulkan_sffi_dispatch_buffer_compute_checked` | `fail`; `backend=vulkan`; wire reason `16` for submit/dispatch; handle `0`; no device readback | Assert no positive provenance/identity, no device readback, and no pass status | Source-matched native init and submit phases pass |
| Readback | `VulkanBuffer::copy_to_staging` inserts compute-shader-write/transfer-write -> transfer-read synchronization before `vulkan_sffi_read_buffer_bytes`; compute and transfer submissions share one mutex for their common queue; then require `bytes.len() == byte_count`; render path `engine.read_pixels_with_source` | `fail`; wire reason `17`; handle `0`; no output checksum | Reject unsynchronized, short, or empty bytes and every pass whose source is not device readback | Barrier mask unit passes 1/1; strict relinked native exact readback and fault phase pass on RTX A6000 |
| Mismatch | Processing `processing_ir_output_matches(ir, values)`; Draw IR canonical checksum check before render | `fail`; wire reason `11`; handle `0`; no device-backed pass | Assert mismatch is non-pass and forged output is rejected | Source-matched native mismatch phase passes |
| Explicit fallback | `_process_request` calls `_processing_cpu_fallback` after executor failure or mismatch only when `--processing-fallback=cpu` | `fallback`; CPU readback; original GPU reason; zero native handle/identity; correlated generation/run/frame/backend | Reject a CPU-backed `pass`; accept fallback only when policy explicitly requests it and correlation fields match | Policy and guest wire validator implemented; end-to-end daemon wire run pending |

### Metal

| Fault | Concrete injection point | Status and receipt fields | Fail-closed assertion | State |
|---|---|---|---|---|
| Unavailable | Guarded `unavailable` phase before Metal availability/init; actual `metal_sffi_is_available() == false` returns `metal-unavailable`; render creation is the platform Engine2D owner | `unsupported`; `backend=unavailable`; handle `0`; no device readback | Linux/unavailable output is not a Metal pass; reject any pass without Metal provenance, identity, and device readback | Guarded seam and runtime-unavailable distinction implemented; prepared-macOS live run pending |
| Init/submit | Init: `metal_sffi_create_device`, queue, shader, pipeline, or allocation; submit: `metal_sffi_run_compute_frame` | `fail`; `backend=metal`; non-empty init/submit reason; handle `0`; no device readback | Accept only as failed; assert no pass, positive provenance, or device readback is emitted after the injected error | Guarded init/submit seams implemented; prepared-macOS live run pending |
| Readback | `metal_buffer_download_ptr`, exact `processing_ir_output_matches`, and checksum `135272480`; render `read_pixels_with_source` | Success requires eight exact values, fixed checksum, and positive provenance; failure has `reason=readback-failed` or `readback-size-mismatch`, handle `0`, and zero output | Reject short or equal-length corrupt readback, absent checksum, absent identity, or any source other than `device_readback` | Host-independent exact-output contract passes; prepared-macOS live run pending |
| Mismatch | Host `processing_ir_output_matches(ir, values)` / Draw IR canonical checksum; synthetic checker `mismatch` receipt | `fail`; `backend=metal`; `reason=checksum-mismatch`; handle `0`; no device-backed pass | Assert failed status and exact reason; reject CPU masquerading and altered output checksum | Guarded mismatch seam implemented after valid readback size; prepared-macOS live run pending |
| Explicit fallback | `_process_request` calls `_processing_cpu_fallback` after executor failure or mismatch only when `--processing-fallback=cpu` | `fallback`; CPU readback; original GPU reason; zero native handle/identity; correlated generation/run/frame/backend | Reject a CPU-backed `pass`; fallback is valid only with explicit policy and correlated IDs | Policy and guest wire validator implemented; prepared-macOS end-to-end run pending |

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

The policy implementation and guest validator are covered by
`processing_cpu_fallback_policy_contract_spec.spl` and
`host_gpu_ivshmem_fallback_receipt_spec.spl`. The native daemon-wire harness is
implemented by `processing_cpu_fallback_daemon_wire_spec.spl` and
`simpleos_gpu_fallback_wire_probe.spl`. Writable mmap ABI normalization, the
native mmap smoke, and separately bounded HELLO/request waits pass
incrementally. The Linux CUDA submit-injection row publishes exact fallback
reason `16`, CPU source `2`, zero handle/identity, 32 bytes, and checksum
`135272480`. Linux CUDA now also passes one same-process exact
success/readback-failure/recovery sequence with stable device identity. Linux
Vulkan passes unavailable, init, submit, readback, and mismatch injection
through the retained native transport, plus its same-process
success/failure/recovery sequence. Its storage-buffer readback now carries an
explicit shader-write/transfer-write to transfer-read barrier, and the strict
relinked probe passes on the RTX A6000. The remaining evidence gap is the Metal
live row on prepared macOS. Linux may run the
validator and source-contract cases, but cannot close Metal runtime evidence.
