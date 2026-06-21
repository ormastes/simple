# Native SFFI file byte I/O: [u8] marshalling broken

**Filed:** 2026-06-20
**Updated:** 2026-06-21 (Round 8 — FIXED in runtime_native.c; no bootstrap needed)
**Status:** RESOLVED for the `rt_file_read_bytes` / `rt_file_write_bytes`
primitives. One downstream follow-up remains (see "Remaining").
**Priority:** P1

## RESOLVED (2026-06-21)

The native `--compile` path links the **C** runtime (`src/runtime/runtime_native.c`,
compiled fresh per build via `build_core_c_runtime_library`), NOT the Rust
`file_ops.rs` (which was already correct) — so this was a plain C fix, **no
bootstrap required**. Confirmed empirically by an in-function diagnostic:

- The codegen lowers `text` as `(ptr, len)` and `[u8]` as `(ptr, len)`, so
  `rt_file_write_bytes(path: text, data: [u8])` is a **4-argument** C call
  `(path_ptr, path_len, data_ptr, data_len)`. The old C signature had only **3**
  params `(const char*, const void*, int64_t)` — off by one — so `data` received
  `path_len` and `len` received the data pointer → 0-byte writes. Fixed to the
  4-param signature; writes exactly `data_len` bytes (NULs included).
- `rt_file_read_bytes` returned a NUL-terminated `char*` (wrong type for `[u8]`,
  and truncated at the first zero byte). Compiled `[u8]` is a byte `SplArray*`
  (as `rt_bytes_from_raw`), so it now returns a binary-safe `SplArray*` read by
  file size.

Verified under `--compile --force-rebuild`:
`test/01_unit/lib/nogc_sync_mut/sffi/native_byte_io_spec.spl` — byte-value
round-trip, embedded-NUL preservation, and all-256-values, 3/3, mutation-checked
(a flipped expected value correctly fails).

## Remaining

Fully un-gating the svllm FS byte tests
(`std_fs_transport_spec.spl`, `svllm_fs_loader_system_spec.spl`) is blocked by a
SEPARATE, pre-existing compiled-mode issue this fix merely EXPOSED (those tests
never ran under `--compile` before): reading bytes through
`StdFsNvfsClient.read_bytes` (which returns `Result<[u8], NvfsError>`) and then
`unwrap()`-ing and indexing the array SIGSEGVs in native mode, while the direct
`file_read_bytes(...) -> [u8]` path works. This is a `Result<[u8]>` unwrap/index
codegen problem, not an SFFI marshalling one. Those byte tests stay gated until
it is fixed; the rt_file primitives themselves are proven.

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

> **Round 9 (2026-06-21):** the rt_file byte primitives are fixed+proven
> (`native_byte_io_spec.spl`, 3/3 under `--compile`). What still blocks the
> svllm byte tests is a distinct, now precisely-diagnosed codegen bug —
> cross-module generic `Result<[u8], E>` payloads lose their static element
> type under native AOT. Full mechanism, reproducers, and the landed transport
> hardening are tracked in
> `native_codegen_crossmodule_generic_result_u8_erasure_2026-06-21.md`.

## Root Cause (diagnosed 2026-06-21, Round 8)

The native runtime byte functions are **Rust**, not C. `bin/simple test
--compile` links the cargo runtime archive
(`src/compiler_rust/target/bootstrap/libsimple_native_all.a`), NOT
`src/runtime/runtime_native.c` — that C file is OFF the `--compile` path (its
symbol is not even exported in the core-C archive). The relevant functions are
`rt_file_read_bytes(path_ptr, path_len) -> RuntimeValue` and
`rt_file_write_bytes(path_ptr, path_len, data_ptr, data_len) -> bool` in
`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`.

`rt_file_read_bytes` is actually correct (binary-safe `std::fs::read` +
`bytes_to_runtime_array`) — the round-7 "returns char*" note described the
irrelevant C file. The real failure is on **write**: the compiled test creates
the output files but they are **0 bytes** (`xxd`-confirmed). `std::fs::write`
is fine, so the slice it receives is empty — i.e. the **self-hosted backend**
(`bin/simple`, used by `--compile`) passes the `[u8]` argument to
`rt_file_write_bytes` WITHOUT a correct length. It is declared
`declare i1 @rt_file_write_bytes(ptr, ptr, i64)` at
`src/compiler/70.backend/backend/llvm_backend.spl:378`; the length the runtime
sees is 0/garbage → 0-byte write.

This is a **codegen/runtime ABI disagreement**, not a runtime-only bug:
- The standard `[u8]` extern convention passes a single tagged array handle
  (`rt_bytes_to_text(bytes: RuntimeValue)` works).
- `rt_file_write_bytes` is declared/lowered with a flattened data shape that
  does not carry the real length.
- Changing ONLY the runtime signature to take a handle (`data: RuntimeValue`)
  makes it **SIGSEGV** (verified — `rt_array_len` dereferences a value that is
  not a valid tagged handle). So the runtime and the backend must change
  together.

## Fix Options

1. Align the self-hosted backend's `rt_file_write_bytes` declaration + call
   lowering (`src/compiler/70.backend`) with the runtime signature so the `[u8]`
   length (or a real tagged handle) reaches the runtime; rebuild `bin/simple`
   (`scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple`) + smoke gate;
   keep the Rust-seed codegen (`runtime_sffi.rs:1514` + `calls.rs` flatten
   special-cases) consistent. Verify with an isolated native byte round-trip
   spec (incl. an embedded-NUL case) under `--compile --force-rebuild`.
2. Until fixed: svllm FS byte reads/writes are interpreter-only; the FS
   transport byte tests stay gated under `--compile` (text-read + error paths
   run natively).

## Status

Open — root cause precisely located (the self-hosted backend does not pass the
`[u8]` length to `rt_file_write_bytes`; runtime-only changes crash). Full fix
needs a coordinated backend codegen change + `bin/simple` bootstrap, deferred as
a larger change. svllm std.fs adapter + transport remain interpreter-verified
(Round 7); native byte FS I/O still blocked here.
