# os__(src/os/services/vfs/vfs_init.spl)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SIMPLEOS-M5-001"></a>FR-SIMPLEOS-M5-001 | VFS select-file cursor semantic (VfsCursor singleton) | `rt_fat32_select_file` (retired in M5) held a static 64-byte name cursor that callers used to remember the last-selected file before operating on it. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
