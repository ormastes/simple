# SimpleOS Host GPU Protocol

## Purpose

Verify the bounded ivshmem protocol, backend and ISA decoding, batch limits,
receipt provenance, and failure/fallback validation.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/01_unit/lib/common/gpu/simpleos_host_gpu_protocol_spec.spl \
  --mode=interpreter
```

## Checks

1. Wire offsets remain aligned and bounded.
2. Vulkan, Metal, DirectX, CUDA, and CPU codes round-trip to exact names and
   masks.
3. x86_64, AArch64, and RISC-V codes round-trip to exact ISA names.
4. Device passes require native provenance and device readback.
5. Explicit CPU fallback has distinct status and CPU readback codes.
6. Stale, malformed, oversized, and synthetic receipts fail closed.
