# nvfs__(examples/11_advanced/nvfs/src/core/encryption.spl_+_arena.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NVFS-N6a-003"></a>FR-NVFS-N6a-003 | DEK rotation on arena seal | On `arena_seal_impl`, if the arena is registered as encrypted in the `EncryptionInfo` registry, derive a fresh DEK (bumped generation) and update | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
