# ProcessingIR Fault Source Contract

## Purpose

Verify that CUDA, Vulkan, and Metal ProcessingIR executors use the same
disabled-by-default fault-injection helper and expose the `init`, `submit`,
`readback`, and `mismatch` phases.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl \
  --mode=interpreter
```

## Checks

1. Every executor imports `processing_ir_fault_reason`.
2. Every executor checks `unavailable`, `init`, `submit`, `readback`, and
   `mismatch`.
3. The helper requires both `SIMPLE_GPU_TEST=1` and an exact
   `SIMPLE_GPU_FAULT_INJECT=<backend>:<phase>` value. The optional exact value
   `SIMPLE_GPU_FAULT_INJECT_SKIP_MATCHES=1` skips only the first matching
   invocation, allowing HELLO admission before an injected request failure;
   changing the exact backend/phase target resets that delay.
4. Vulkan and Metal return non-owning device provenance rather than freed
   resource identifiers.
5. Branch-local ordering checks prove Metal cleanup precedes each queue,
   shader, pipeline, allocation, submit, dispatch, readback, size-mismatch,
   mismatch-injection, and success return.
6. CUDA keeps real dispatch and readback failures distinct.

This is a host-independent source contract. It does not replace live device
execution.

Execution status: Linux Rust-seed interpreter pass, 6/6. Prepared-host Metal
failure injection remains pending on macOS.
