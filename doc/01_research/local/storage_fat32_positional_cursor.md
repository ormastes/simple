# FAT32 Positional Cursor Preservation - Local Research

## Scope

Feature request: `FR-STORAGE-0002` in `doc/08_tracking/feature_request/nvfs_requests.md`.

## Findings

- `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` had `pass_todo` bodies for `pread` and `pwrite`.
- The wrapper delegates to `src/os/services/fat32/fat32.spl`, where open-file state includes `current_offset` and `current_cluster`.
- `Fat32Core.write` already updates open-file cursor state, but `seek` did not persist the new cursor and `read` did not advance it.
- Cursor-preserving positional I/O can be implemented without new disk primitives by saving the open-file cursor, seeking, performing read/write, then restoring only cursor fields. File-size changes from `pwrite` must be preserved.

## Selected Fix

- Persist cursor updates in `Fat32Core.seek`.
- Advance cursor after `Fat32Core.read`.
- Add `Fat32Core.restore_open_file_cursor`.
- Implement wrapper `Fat32Driver.pread` and `pwrite` as save/seek/read-or-write/restore.

## Regression Surface

- System SSpec: `test/system/storage_fat32_positional_cursor_spec.spl`
