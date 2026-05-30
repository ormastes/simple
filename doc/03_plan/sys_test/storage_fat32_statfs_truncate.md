# System Test Plan — storage_fat32_statfs_truncate

Spec: `test/system/storage_fat32_statfs_truncate_spec.spl`

Coverage:
- Synthetic FAT sector with two free entries verifies `count_free_clusters()`.
- `truncate_chain(first_cluster, 0)` verifies whole-chain truncation returns an empty
  first-cluster marker.

Acceptance mapping:
- FR-STORAGE-0001 AC1: free-cluster counting supplies `statfs` free-space data.
- AC2/AC3: truncate/ftruncate are wired through `truncate_chain` and metadata updates.
- AC4: focused source checks cover the affected FAT32 and FsDriver files.
