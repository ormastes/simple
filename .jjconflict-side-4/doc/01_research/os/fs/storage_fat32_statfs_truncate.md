# Local Research — storage_fat32_statfs_truncate

Feature request: `FR-STORAGE-0001`.

Findings:
- `Fat32WriteContext` already had `read_fat_entry`, `write_fat_entry`, `allocate_cluster`,
  `extend_chain`, `free_chain`, and `update_file_size`.
- `Fat32Driver` already stores mounted geometry needed for `statfs`: `total_clusters`,
  `sectors_per_cluster`, and `bytes_per_sector`.
- The missing pieces were a free-cluster count, a shrink/free helper that can cut a chain,
  and FsDriver wrapper delegation.

Implementation scope:
- Add `count_free_clusters()` to the core FAT32 driver.
- Add `truncate_chain()` and metadata update support to `Fat32WriteContext`.
- Wire `FsFat32Driver.statfs`, `truncate`, and `ftruncate`.
