# FAT32 Positional Cursor Preservation - System Test Plan

## Request

Cover `FR-STORAGE-0002`: FAT32 positional `pread` / `pwrite` must not leave the open-file cursor at the positional offset.

## Test

`test/system/storage_fat32_positional_cursor_spec.spl`

## Assertions

- `seek(handle, 0, Set)` persists `current_offset = 0` in the open-file table.
- `restore_open_file_cursor(handle, saved_cluster, saved_offset)` restores cursor fields.
- Cursor restore preserves file-size growth, which is required after `pwrite`.

## Verification Command

`bin/simple test test/system/storage_fat32_positional_cursor_spec.spl`
