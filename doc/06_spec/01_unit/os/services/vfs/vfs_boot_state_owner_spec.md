# VFS Boot State Ownership Contract

Source: `test/01_unit/os/services/vfs/vfs_boot_state_owner_spec.spl`

Evidence class: `source-contract`.

## Scenario

- Verify that mutable class-global VFS boot state is declared and mutated only
  by `vfs_boot_state.spl`, while boot, ambient-context, NVMe, and FAT helpers
  reach it through the owner interface.

This is an ownership boundary check, not live NVMe or FAT32 execution evidence.

