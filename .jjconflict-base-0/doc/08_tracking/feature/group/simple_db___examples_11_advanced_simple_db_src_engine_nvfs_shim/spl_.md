# simple_db__(examples/11_advanced/simple_db/src/engine/nvfs_shim.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPOSTGRE-M2-001"></a>FR-SPOSTGRE-M2-001 | Replace duplicated NVFS constants/types in nvfs_shim.spl with real cross-submodule imports | After FR-COMPILER-003 (2-pass import resolver), replace duplicated constants and types in `nvfs_shim.spl` with `use examples.nvfs.src.core.<module>.{<name>}` imports. Items in scope: `STORAGE_CLASS_DB_WAL`, `STORAGE_CLASS_META_DURABLE`, `DU | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
