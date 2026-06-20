# Native SFFI file byte I/O: [u8] marshalling broken

**Filed:** 2026-06-20
**Status:** open
**Priority:** P1

## Problem

Under native compilation (`bin/simple test --compile` / `--mode=native`), the
SFFI whole-file byte primitives in `std.nogc_sync_mut.sffi.io` mis-marshal
`[u8]`:

- `rt_file_read_bytes(path) -> [u8]` returns a raw `char*` rather than a tagged
  Simple array, so any `.len()` / index on the result SIGSEGVs (or yields
  garbage) in native mode.
- `file_write_bytes(path, data: [u8])` of a dynamically-built `[u8]` (e.g.
  assembled via `.push(v as u8)`) writes 0 bytes natively.

The **interpreter** path is correct. Verified with a driver (`bin/simple run`):
write `[100,101,102,103,104,105]` via `file_write_bytes`, read back via the
svllm `StdFsNvfsClient.read_bytes` → `len=6, data[0]=100, data[5]=105` (PASS);
absent path → `Err(NotFound)`. So the svllm std.fs read adapter LOGIC is right;
only native SFFI `[u8]` codegen is broken.

The text primitives `file_read_text` / `file_write_text` work natively (the
read_text/write_text path was repaired separately).

## Impact

`svllm` `load_model_from_pack_fs` (Round 7 FS transport) reads chunk bytes via
`StdFsNvfsClient.read_bytes`. The full FS-backed happy path therefore cannot be
verified under `--compile` (the only assertion-executing test mode) until this
is fixed — the byte-dependent tests in
`test/01_unit/lib/nogc_async_mut/svllm/nvfs_client/std_fs_transport_spec.spl` and
`test/03_system/tools/svllm_fs_loader_system_spec.spl` are gated/skipped with a
reference to this doc. Text-read + error-path assertions still run natively.

## Root Cause (suspected)

Native runtime `rt_file_read_bytes` returns the C buffer pointer without
wrapping it in the tagged SplArray representation the codegen expects for
`[u8]`; and the native `rt_file_write_bytes` extern does not read length/data
from a heap-built `[u8]` correctly (writes 0 bytes). Likely the same
`[u8]`-return/argument marshalling family as other native byte-boundary bugs
(see `feedback_text_only_byte_cliffs`, native byte-handling notes).

## Fix Options

1. Fix native `rt_file_read_bytes` to return a tagged `[u8]` (allocate + tag +
   copy length), and `rt_file_write_bytes` to read len/ptr from the tagged
   array argument.
2. Until fixed: svllm FS byte reads are interpreter-only; the FS transport
   tests assert text-read + error paths natively and defer byte-value /
   happy-path byte assertions to the interpreter driver.

## Status

Open. svllm Round 7 std.fs read adapter + transport are implemented and
interpreter-verified (incl. byte values); native byte FS I/O blocked here.
