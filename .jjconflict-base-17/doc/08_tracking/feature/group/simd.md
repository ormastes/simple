# simd

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-SIMD_INT_INTRINSICS_FOR_CRYPTO_2026_05_01"></a>SIMD_INT_INTRINSICS_FOR_CRYPTO_2026_05_01 | Feature: extend SIMD surface with int bitwise / rotate / shuffle ops for crypto | **Status: CLOSED** — All phases landed (2026-05-02). No further action needed. > **AES-256 SIMD path LANDED 2026-05-02 — 14 rounds via W6-A externs.** `aes256_encrypt_block` in `src/os/crypto/aes256_gcm.spl` now wires through `simd_aes_roun | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-SIMD_U32X4_I64X4_INTRINSICS_2026_05_02"></a>SIMD_U32X4_I64X4_INTRINSICS_2026_05_02 | FR: Vec4u32 and Vec4i64 SIMD Intrinsics | # Wave L / L4 — 2026-05-02 # **Status: IMPLEMENTED 2026-05-10** — structs, externs, wrappers, and aliases landed. ## Summary Add `rt_simd_*_u32x4` (8 ops) and `rt_simd_*_i64x4` (8 ops) extern primitives to the Rust runtime, with correspondi | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
