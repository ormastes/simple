# Seed: GetVolumeInformationW is not a registered Windows ABI extern

Date: 2026-11-26. Found by lane P2 (SOSIX contained launch).

`GetVolumeInformationW` is missing from the `NAMES` list in
`src/compiler_rust/compiler/src/interpreter_extern/windows_abi.rs`, so the seed
interpreter cannot serve it. P2 therefore cannot check `FILE_PERSISTENT_ACLS` (0x8)
as architecture pure_simple_container 4.2 names for `containment-volume-no-acl`.

Repro (seed `simple-local-20261126.exe`): declare
`@abi("system") extern fn GetVolumeInformationW(root: i64, name: i64, name_len: u32, serial: i64, max_component: i64, flags: i64, fs_name: i64, fs_name_len: u32) -> i32`
and call it from code run under `simple test` (or any interpreted run). Result:

    semantic: <file>:<line>:<col>: unknown extern function: GetVolumeInformationW

The same call works under `simple run` of a script with `fn main` (JIT path), which
shows the failure is the interpreter registry, not the API.

Current fallback in `src/lib/nogc_sync_mut/sosix/windows/containment_launch_v1.spl`:
the DACL must be readable and non-NULL for every dir, writable dirs must read back the
low label, readonly dirs must carry the reader ACE and no low label. It is untested on
a FAT/exFAT volume. Fix: add `GetVolumeInformationW` to `NAMES` and dispatch, then
check the 0x8 flag for every dir in `_acl_refusal_v1`.
