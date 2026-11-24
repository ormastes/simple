# bytes_to_text must reject invalid UTF-8 (owner decision 2026-11-23)

Status: open (PR1 of 3 landed: API + SOSIX; runtime parity and callers pending)

## Defect
Lanes disagree on malformed input to `rt_bytes_to_text`:
- Rust runtime `value/sffi/file_io/file_ops.rs` (~2370): `String::from_utf8_lossy` (U+FFFD).
- Seed interpreter `interpreter_extern/conversion.rs:175`: keeps raw bytes as a text carrier.
- C runtime (`runtime.c`, `runtime_core_io_exports.c`, `runtime_native.c`): raw copy.

So a "text" could hold non-UTF-8 bytes, and `sosix/text_boundary_spec` failed 2/9
(`semantic: type mismatch: cannot convert str to int`, raised while the seed
re-extracted bytes from the raw `bytes_to_text([65u8,255u8])` carrier).

## Decision
`text` is always valid UTF-8. Invalid input is rejected everywhere: no lossy
U+FFFD, no raw-byte carrier.

- **Checked API (canonical):** `std.common.encoding.external_text.bytes_to_text_checked(bytes: [u8]) -> Result<text, CodecError>`
  = `external_text_decode(bytes, utf8_format())`. Errors follow the existing
  codec convention: `CodecErrorKind.InvalidUtf8` / `TruncatedInput` with
  `byte_offset` (first bad byte for a stray byte, e.g. `[65,255]` -> 1).
  It lives beside `external_text` (not in `text_bytes`) because `CodecError`
  is defined there and `external_text -> text_bytes` is the existing import edge.
- **Infallible `std.common.text_bytes.bytes_to_text`: deprecated, then removed.**
  There is no total, panic-free, non-lossy `[u8] -> text`. Returning `""` would be
  the silent-failure class this repo files bugs about, and panicking violates
  panic-free safe code. So it cannot "fail closed" while keeping its signature.
- **Runtime primitive:** `rt_bytes_to_text` follows the repo's fallible-primitive
  shape (`rt_byte_array_new -> [u8]?`, `rt_array_concat -> [u8]?`): it returns nil
  on invalid UTF-8 in every lane (Rust `from_utf8`, seed, C, Simple twin), and
  the extern is declared `-> text?`, consumed only in `unsafe` or via `if val`.
- **SOSIX:** unvalidated provider input enters as `[u8]` through
  `sosix_admit_utf8_bytes`, which returns `TextIoError.Codec(CodecError)`.
  `sosix_admit_utf8(text)` remains for already-internal text.

## Staging (split per >1h rule)
1. **PR1 (this):** `bytes_to_text_checked`, deprecation note, `sosix_admit_utf8_bytes`,
   SOSIX spec rewritten to build malformed input as bytes and assert the precise
   codec error; parity spec `test/01_unit/lib/common/encoding/bytes_to_text_checked_spec.spl`.
2. **PR2 runtime parity:** Rust runtime + seed interpreter + C runtime (+ extend
   `src/runtime/test/rt_bytes_to_text_layouts_selfcheck.c`) + `simple_core/core_array.spl`
   reject -> nil; check codegen builtin lowering (`codegen/llvm/functions/calls.rs`,
   `codegen/instr/calls.rs`, `tests/text_static_builtins_jit.rs`). Parity spec gains
   a compiled-path case. Needs seed cargo build (own target dir, CC=clang-cl).
3. **PR3 callers:** ~940 uses / 344 files, ~25 files redeclare `extern fn rt_bytes_to_text`
   (some with `[i64]`). Migrate to `bytes_to_text_checked` and handle `Err`; binary
   carriers (linker/sshd/kernel) must stay `[u8]` rather than going through text. Then
   delete `text_bytes.bytes_to_text`. PR2 must land together with or after PR3 for
   binary-carrier callers, or they break at runtime.

## Evidence (PR1, Rust seed interpreter, Windows)
- `test/01_unit/lib/nogc_async_mut/sosix/text_boundary_spec.spl`: 7/9 -> 9/9.
- `test/01_unit/lib/common/encoding/bytes_to_text_checked_spec.spl`: 3/3.
- Note: the strict codec reports overlong/surrogate offsets inside the sequence
  (`[0xC0,0x80]` -> 1), so the spec pins the offset only for the stray-byte case.

## PR3 slice: kernel ipc + vfs (2026-11-23)
- New `src/os/kernel/text_checked.spl`: `kernel_text_checked(bytes) -> Result<text, i32>`
  (Err(EILSEQ=84), added to `os.kernel.errno`). Validation is pure Simple because the
  freestanding runtimes (`arch/*/freestanding_runtime.c`) do not define
  `rt_utf8_validate`, so `text_bytes.utf8_bytes_valid` would be an unbacked extern
  in-kernel; `rt_bytes_to_text` is defined there and is reached only on validated input.
- Converted: `ipc/syscall_file.spl` (8 path decodes -> `_FS_EILSEQ`),
  `ipc/syscall_process.spl` (spawn/exec paths -> -EILSEQ; dlopen/dlsym and argv/envp
  cstrs -> existing Err text path), `ipc/syscall_ipc.spl` (port name -> nil),
  `services/vfs/vfs_dispatch.spl` (read_file_text: invalid -> "" instead of a
  per-byte Latin-1 decode), `services/vfs/nvfs_connector.spl` (read_text -> InvalidArg).
- Remaining kernel/vfs sites: vfs_boot_state, vfs_init, direct_fat32_boot_reader,
  nvme_q35_lease_perf (all via vfs_boot_state/vfs_init `_vfs_bytes_to_text`),
  vfs_include_tree_proof_v1, loader/executable_source, loader/app_registry,
  loader/signed_catalog_scr1_decoder_v1, loader/simplebox_catalog_media_boot_v1,
  memory/vmm_copy, net/*, arch/*/console + up_squared serial/gdb, cortex_m33 shell_lite,
  security/sandbox_boot_apply.
