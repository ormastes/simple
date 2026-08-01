# SPM pt-walk user-copy Local Research

Feature: FR-SPM-0001.

- `src/os/kernel/ipc/syscall.spl` used `_copy_in_bytes` for SPM byte buffers and
  previously copied through the user virtual address after VMA validation.
- `src/os/kernel/ipc/capability.spl` already registered task vmspaces and
  validated grant ranges with VMA flags, but still documented deferred
  pt-walk-based copy checks.
- `src/os/kernel/memory/vmm.spl` had kernel-global page-table verification and
  copy-in helpers, but no helper that accepted an explicit `ProcessVmSpace`.
- Existing unit specs use `ProcessVmSpace(pml4: 0, ...)` as a no-real-page-table
  fixture; production process spaces are expected to carry a non-zero PML4.
