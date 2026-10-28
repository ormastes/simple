# Windows exclusive link recheck uses 64-bit file index (ReFS not unique) - 2026-10-27

Found by Fable review of PR #5047 (Windows `rt_file_link_create_excl_no_follow`).

`src/runtime/platform/runtime_win_excl_file.h` and `win_excl` in
`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs` compare
`(dwVolumeSerialNumber, nFileIndexHigh, nFileIndexLow)` from
`GetFileInformationByHandle` as the analogue of POSIX `st_dev/st_ino`. On NTFS that
64-bit index is stable and unique per volume. On ReFS file ids are 128-bit and the
64-bit index is not guaranteed unique, so the post-link identity recheck could in
principle accept a different file.

Fix: use `GetFileInformationByHandleEx(handle, FileIdInfo, &FILE_ID_INFO, ...)`
(`VolumeSerialNumber` 64-bit + `FileId` 128-bit) in both the C header and the Rust
twin (`windows-sys` `Win32_Storage_FileSystem` `FILE_ID_INFO`, `FileIdInfo`),
falling back to the 64-bit index only where `FileIdInfo` is unsupported. Add a probe case to
`src/runtime/test/rt_win_excl_file_selfcheck.c`. Not urgent: NTFS is the supported
Windows cache volume today.
