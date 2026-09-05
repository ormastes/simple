# FAT32 Positional Cursor Preservation - Design

## Problem

`FR-STORAGE-0002` requires POSIX-style positional I/O for the FAT32 `FsDriver` wrapper. `pread` and `pwrite` need to operate at the requested offset without changing the file cursor visible to later sequential operations.

## Design

Use the existing FAT32 open-file state as the source of truth.

- `seek` persists the requested cursor in `open_files`.
- `read` advances `current_offset` by bytes read.
- `restore_open_file_cursor` restores `current_cluster` and `current_offset` after a positional operation while preserving the current `file_size`.
- Wrapper `pread` and `pwrite` save cursor state, seek to the requested offset, call core read/write, then restore the saved cursor.

Preserving `file_size` during restore matters for `pwrite`, because a positional write may extend the file while still leaving the caller's sequential cursor unchanged.

## Test Strategy

The system test validates the cursor state transitions directly with a mock block device and synthetic open-file entry. This avoids needing a full FAT32 image while covering the state primitive used by both wrapper positional operations.
