# os-kernel_(src/os/kernel/ipc_+_src/os/kernel/memory)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPM-0001"></a>FR-SPM-0001 | Page-table-walk read primitive for cross-page / non-identity-physmap user reads | Expose a `pt_walk(space: ProcessVmSpace, vaddr: u64) -> u64?` (or equivalent "translate user VA → kernel-readable pointer"") helper in `src/os/kernel/memory/vmm.spl`. Consumers: `_copy_in_bytes` (src/os/kernel/ipc/syscall.spl), `GrantTable.s" | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
