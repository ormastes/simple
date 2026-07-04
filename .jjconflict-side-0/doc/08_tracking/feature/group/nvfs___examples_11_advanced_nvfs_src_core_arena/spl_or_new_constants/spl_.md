# nvfs__(src/os/services/nvfs/src/core/arena.spl_or_new_constants.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPOSTGRE-M2-002"></a>FR-SPOSTGRE-M2-002 | Add named StorageClass and DurabilityClass constants to NVFS core | `src/os/services/nvfs/src/core/arena.spl` uses `class_tag: i32` as an opaque ordinal with no named constants. Consumers (Simple DB, future callers) must either duplicate ordinal assignments or rely on comments that say "matching nvfs i" | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
