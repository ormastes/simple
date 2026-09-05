# Native Backend Failure and Fallback Receipts

## Purpose

Exercise the production SimpleOS GPU batch and receipt validators with
unavailable, failed, mismatched, fallback, and forged provenance cases.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl \
  --mode=interpreter
```

## Checks

1. CUDA, Vulkan, and Metal unavailable receipts remain unsupported.
2. Submit/readback/checksum failures remain non-pass.
3. Failed, unsupported, and blocked receipts reject positive handles,
   identities, device-readback sources, and output payload claims.
4. CPU fallback is accepted only as explicit `fallback` with zero native
   provenance.
5. CPU-backed GPU pass receipts are rejected.
