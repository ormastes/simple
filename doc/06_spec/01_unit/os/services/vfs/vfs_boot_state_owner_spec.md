# VFS Boot State Ownership Contract

Source: `test/01_unit/os/services/vfs/vfs_boot_state_owner_spec.spl`

Evidence class: `source-contract`.

## Scenario

- Verify that mutable class-global VFS boot state is declared and mutated only
  by `vfs_boot_state.spl`, including the hosted root NVFS driver and its
  commit owner, while boot, ambient-context, NVMe, and FAT helpers reach state
  through the owner interface.
- Require root NVFS reads and writes to use the split `nvfs_posix_*_owned`
  operations from `vfs_boot_init.spl` and `vfs_write_ops.spl`; reject the old
  hosted wrappers and direct mount-table or readiness mutation outside the
  state owner.

This is an ownership boundary check, not live NVMe or FAT32 execution evidence.
