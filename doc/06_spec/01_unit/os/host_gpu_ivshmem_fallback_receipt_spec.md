# Host GPU ivshmem Fallback Receipt Spec

## Purpose

Verify that an explicit CPU fallback is distinguishable from a device pass and
retains exact request correlation without claiming native GPU provenance.

## Run

```sh
SIMPLE_LIB=src bin/simple test test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl --mode=interpreter
```

## Checks

1. A correlated fallback with CPU readback, output evidence, and zero native
   handle/identity is accepted.
2. Pass status, zero reason, device readback, forged provenance, invalid output
   evidence, and wrong generation/run/frame/backend are rejected.
