# SPM pt-walk user-copy Design

Feature: FR-SPM-0001.

- Add `vmm_pt_walk_user_read(space, vaddr)` for single-address translation.
- Add `vmm_pt_range_user_readable` and `vmm_pt_range_user_writable` for grant
  range validation.
- Add `vmm_copyin_bytes_from_space(space, ptr, len)` for SPM byte-buffer copy-in.
- Update `_copy_in_bytes` to call the explicit-space helper when
  `g_current_vmspace.pml4 != 0`; preserve the existing pml4=0 compatibility
  path after VMA validation.
- Update `GrantTable.safecopy_from` / `safecopy_to` to reject page-table misses
  for registered vmspaces with non-zero PML4 roots.
