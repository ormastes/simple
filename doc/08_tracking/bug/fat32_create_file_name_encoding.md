# Bug: Fat32Core create_file writes wrong bytes for filenames

**Date:** 2026-05-27
**Severity:** high
**Component:** src/lib/nogc_sync_mut/fs_driver/fat32_dir_ops.spl

## Symptom

Files created via `Fat32Core.create_file()` cannot be found by
`Fat32Core.open()` or `Fat32Core.resolve_path()`. The directory entry IS
written to the block device (visible via `readdir`), but path resolution
fails with "file not found".

After create_file, `close(handle)` and `write(handle, ...)` return
"invalid file handle" — the handle allocated in the free function
`fat32_create_file` does not persist back to the Fat32Core instance.

## Root Cause (two bugs)

### 1. Name encoding (fat32_dir_ops.spl:65)

```spl
val ch = str_char_at(name, ci)
var b: u8 = ch.len().to_u8()   # BUG: writes 1 for every ASCII char
```

`str_char_at` returns a single-character text. `.len()` is always 1.
Every byte in the 8.3 directory entry name becomes `0x01`.

**Fix:** `var b: u8 = name.char_at(ci) as u8`

### 2. Handle persistence (fat32_dir_ops.spl → fat32_core.spl:1075)

`create_file` delegates to free function `fat32_create_file(self, path)`.
In interpreter mode, `self` is copied into the `core` parameter. The free
function calls `core.alloc_file_handle(...)` on the copy — the handle is
never registered on the original Fat32Core instance.

**Fix:** Return cluster numbers from the free function; do handle
allocation and cache invalidation on `self` in the `me fn create_file`
method.

### 3. Same name encoding bug in fat32_mkdir (fat32_dir_ops.spl:134)

Identical `ch.len().to_u8()` pattern.

## Status

**RESOLVED** — all three bugs fixed in both `nogc_async_mut` and `nogc_sync_mut` versions.
All 7/7 benchmark workloads pass. Array value-type semantics required inlining
8.3 encoding directly (no helper function — arrays are copied into function params).

## Impact (before fix)

- fat32_microbench.spl seq_write/seq_read benchmarks produced bogus results
- fat32_vs_cfat_bench.spl: 5 of 7 workloads SKIP
- Any code path using Fat32Core.create_file in interpreter mode was broken
