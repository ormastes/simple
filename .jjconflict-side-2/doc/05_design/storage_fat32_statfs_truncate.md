# Design — storage_fat32_statfs_truncate

`FsFat32Driver.statfs()` computes total bytes from mounted geometry and free bytes from
a core FAT walk.

`Fat32WriteContext.truncate_chain(first_cluster, keep_bytes)` owns FAT mutation:
- `keep_bytes == 0` frees the whole chain and returns first cluster `0`.
- nonzero shrink keeps the required cluster prefix, frees the tail, and marks the new
  last cluster EOC.
- extension can allocate missing clusters up to the requested length.

`Fat32Driver.truncate_path` and `truncate_open_file` call the helper, update directory
metadata, and keep open-file cursors/sizes consistent.
