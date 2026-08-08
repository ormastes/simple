# X25519MLKEM768 local research — TLDR

```sdn
state: { ml_kem: isolated_unverified, tls_hybrid: missing, simd: scalar_hardcoded, gpu: batch_only }
host: { avx2: true, cuda: true, vulkan: true, arm_native: false, riscv_native: false, metal: false }
```

- Pure-Simple ML-KEM-512/768/1024 exists but lacks input validation, complete independent KATs, zeroization, and production callers.
- TLS supports X25519/P-256 only; `0x11ec` is not wired.
- X25519 has hot-loop logging and secret-dependent branching.
- SIMD detection is hardcoded to scalar and its configuration models disagree.
- ProcessingIR cannot represent typed crypto buffers; GPU setup is currently per-call.
- CUDA/Vulkan are locally available; native ARM/RVV/Metal evidence needs external hosts.
- Coverage tooling cannot currently prove the requested 98% branch target.
- Three real suites are required: absolute KAT/negative, cross-backend same-fixture, and TLS system/interoperability.

