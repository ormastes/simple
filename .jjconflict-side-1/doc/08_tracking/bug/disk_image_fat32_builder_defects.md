# BUG: disk_image.spl FAT32 builder — 4 defects (payload iteration, silent truncate, dirent 8.3, FAT overflow)

**Status:** open (all pre-existing; found while producing a >4 MiB streaming-loader test image)
**Severity:** medium-high (each silently produces an unusable/invalid image or blocks builds)
**Component:** `src/os/port/disk_image.spl` (+ one interpreter extern)
**Found:** 2026-07-11 (streaming PT_LOAD loader lane)

## 1. Payload-array iteration requires explicit `nested_payloads: []`

`DiskImageConfig(size_mb: 2, payloads: [PayloadEntry(...)])` (omitting `nested_payloads`) →
`build()` fails "semantic: cannot iterate over this type" at `for p in cfg.payloads:`.
Workaround: always pass `nested_payloads: []` explicitly.

## 2. `rt_file_truncate` silent no-op in-builder-context

`build()` with `size_mb: 32` writes the full structural prefix then errors "truncate failed",
yet the identical `rt_file_truncate(path, 32u64*1024u64*1024u64)` succeeds standalone,
cross-module, and on the same path/size (verified 3 ways). Context-dependent boxed u64 arg
falls through the `Value::Int` match at
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:908` and silently returns
`Bool(false)` — no error, no set_len.

## 3. Dirent names stored verbatim-with-dot instead of 8.3

`build()` (~line 371) passes `p.path` verbatim to `_build_dir_entry`: "FSEXECBG.ELF" is
stored as the 11 bytes "FSEXECBG.EL" (dot kept, truncated) while the C reader matches proper
8.3 "FSEXECBGELF" → `fat32_find_file` never matches any name with a dot at position ≠8.
Repro: build an image with a 12-char payload name, `xxd` the root dirent.

## 4. FAT overflow for payloads >8,387,072 bytes

FAT is fixed at 128 sectors = 16,384 entries ≈ 8.39 MB at 512 B/cluster. A larger payload's
cluster chain silently overruns FAT1→FAT2→root dir (root dir shifted 104 bytes, volume
unreadable). Repro: `build()` a payload >8,387,072 bytes and check bytes at 0x24000 are FAT
values, not dirents. Fix: size FAT sectors from `size_mb` (or error out).
