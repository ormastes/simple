# BUG: disk_image.spl FAT32 builder — 4 defects (payload iteration, silent truncate, dirent 8.3, FAT overflow)
## RESOLVED 2026-07 — verified 2026-11-25

**Status:** resolved (fixed by 2138b3d9fca "fix(disk-image): FAT32 builder —
field default, truncate u64 unbox, 8.3 names, dynamic FAT sizing"; the
"Open 2026-09-16" header below is a stale pre-fix revision resurrected by
the 2026-09 tree transplant 88aac2ffe28).

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Verification note 2026-11-25 (p2w2-aj)

All four defects confirmed fixed on release/1.0.0 HEAD by code inspection:

1. **Payload-array iteration** — `DiskImageConfig.nested_payloads` now has a
   default (`src/os/port/disk_image.spl:62`, `= []`), so omitting it no longer
   breaks `for p in cfg.payloads:` iteration.
2. **`rt_file_truncate` silent u64 no-op** — the extern now accepts
   `Value::UInt { value, .. }` as well as `Value::Int`, and hard-errors on a
   genuinely bad arg type
   (`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:2094-2117`),
   with regression tests `truncate_accepts_boxed_u64_size_arg`,
   `truncate_accepts_plain_int_size_arg`, `truncate_errors_on_non_integer_size_arg`
   in the same file (Rust `#[test]`s, not runnable from this seed-only host).
3. **Dirent 8.3** — `_split_83_name` (`disk_image.spl:131`) converts
   "FSEXECBG.ELF" to proper 8.3 before `_build_dir_entry`; VFAT long-name
   slots handle non-8.3 names.
4. **FAT overflow** — FAT sectors are sized dynamically from the total data
   cluster count (`disk_image.spl:666-692`), with an explicit Err when the
   image cannot hold FAT+root+data instead of silent overrun.

Execution verification limit: `bin/simple.exe test
test/01_unit/os/port/disk_image_builder_spec.spl --mode=interpreter` fails
repo-wide at HEAD with `unknown decorator '@representation_boundary'`
(source/binary inconsistency between the pinned v1.0.0-rc.1 Rust seed and
release/1.0.0 sources, commit cfd89933699). The Rust-side regression tests
(#2) require a cargo build, which is out of scope for this lane. Verified by
code inspection against the fix commit 2138b3d9fca.
