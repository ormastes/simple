# ecdsa

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-ECDSA_P384_P521_RUNTIME_PRIMITIVES_2026_05_02"></a>ECDSA_P384_P521_RUNTIME_PRIMITIVES_2026_05_02 | ECDSA-P-384 + ECDSA-P-521 primitives for TLS 1.3 | **Filed:** 2026-05-02 **Filed by:** W11-C (TLS 1.3 sigalg coverage track) **Modules:** - `src/lib/nogc_sync_mut/io/signature_ffi.spl` (FFI extern path) - `src/os/crypto/ecdh_p384.spl`, `ecdsa_p384.spl`, `ecdh_p521.spl`, `ecdsa_p521.spl` (pu | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
