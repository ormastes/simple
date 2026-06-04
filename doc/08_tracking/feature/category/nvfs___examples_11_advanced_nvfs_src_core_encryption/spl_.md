# nvfs__(examples/11_advanced/nvfs/src/core/encryption.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NVFS-N6a-001"></a>FR-NVFS-N6a-001 | Wire real AES-128-GCM into NVFS leaf DEK encrypt/decrypt | `encryption.spl` stubs (`_aes128_encrypt_stub` / `_aes128_decrypt_stub`) use XOR + checksum instead of real AES-128-GCM. Replace with calls to | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-NVFS-N6a-002"></a>FR-NVFS-N6a-002 | KDF hardening: salted derivation for per-arena dataset keys | `_derive_data_key_bytes` used a plain XOR of master_key bytes and arena_id with no domain separation or salt. Upgrade to a salted derivation that includes | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
