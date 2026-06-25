# nvfs__(src/os/services/nvfs/src/core/compression.spl_—_new)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NVFS-N7a-001"></a>FR-NVFS-N7a-001 | Inline compression: per-arena LZ4/Zstd, class-aware defaults | Add an inline compression layer (N7a) between the logical block and the physical device. Compression is per-dataset, per-arena, and opt-in via mount option `compress=<algo>` | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
