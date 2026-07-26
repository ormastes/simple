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

## Backend Matrix

| Backend | Unavailable | Invalid request | Submit failure | Readback mismatch | Explicit CPU fallback |
|---|---|---|---|---|---|
| CUDA | `unsupported`, no fallback | `fail/invalid-request` | `fail/submit-failed` | `fail/checksum-mismatch` | `fallback/cpu` only by policy |
| Vulkan | `unsupported`, no fallback | `fail/invalid-request` | `fail/submit-failed` | `fail/checksum-mismatch` | `fallback/cpu` only by policy |
| Metal | `unsupported`, no fallback | `fail/invalid-request` | `fail/submit-failed` | `fail/checksum-mismatch` | `fallback/cpu` only by policy |

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

## Missing Injection Hook

No repository-owned environment variable, CLI option, or backend adapter hook
currently forces `backend-unavailable`, `submit-failed`, or
`checksum-mismatch` in `src/app/simpleos_gpu_host/main.spl` or the CUDA,
Vulkan, and Metal ProcessingIR adapters. The protocol has no canonical
`submit-failed` fault producer. The new spec therefore validates injected
failure receipts at the canonical checker boundary; a follow-up implementation
task is required for live fault injection and end-to-end daemon receipt tests.
