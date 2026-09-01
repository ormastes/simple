# Bug: `rt_unix_socket_*` extern shape mismatch (.spl text ABI vs Rust ptr/len ABI)

- **Date:** 2026-08-26
- **Found by:** Wave-4 SCV lane A (E-09 editor IPC transport bring-up)
- **Status:** FIXED 2026-08-27 (`.spl` side, no seed rebuild needed for the
  JIT/native lane). One lane remains blocked on a seed rebuild — see
  "Residual gap" below.

## Symptom
`rt_unix_socket_listen` / `rt_unix_socket_connect` return `-22` (EINVAL);
`rt_unix_socket_recv` core-dumps.

## Root cause
The Simple extern declarations in
`src/lib/nogc_sync_mut/service/extern.spl` (lines 13-20) declare a
text-shaped ABI:

```
extern fn rt_unix_socket_connect(path: text) -> i64
extern fn rt_unix_socket_listen(path: text, backlog: i64) -> i64
extern fn rt_unix_socket_send(fd: i64, data: text) -> i64
extern fn rt_unix_socket_recv(fd: i64, max_bytes: i64) -> text
extern fn rt_unix_socket_close(fd: i64) -> bool
```

but the Rust runtime implementation in
`src/compiler_rust/runtime/src/value/net_uds.rs` implements a
(ptr,len)/out-param ABI with an explicit buffer-free function:

```
pub unsafe extern "C" fn rt_unix_socket_listen(path_ptr: i64, path_len: i64, backlog: i32) -> i64   // :71
pub unsafe extern "C" fn rt_unix_socket_send(fd: i64, data_ptr: i64, data_len: i64) -> i64          // :122
pub unsafe extern "C" fn rt_unix_socket_recv(fd: i64, max_len: i64, out_len: *mut i64) -> i64       // :148
pub unsafe extern "C" fn rt_unix_socket_free_buf(ptr: i64, len: i64)                                // :193
pub extern "C" fn rt_unix_socket_close(fd: i64) -> i32                                              // :203
pub unsafe extern "C" fn rt_unix_socket_connect(path_ptr: i64, path_len: i64) -> i64                // :227
```

Only `rt_unix_socket_accept(fd: i64) -> i64` (:97) matches. A text value
passed where `(path_ptr, path_len)` is expected yields a garbage path →
`-22` EINVAL from listen/connect; `recv` interprets the missing
`out_len: *mut i64` out-param and returns a raw pointer where the caller
expects `text` → core dump. `rt_unix_socket_free_buf` has no `.spl`
declaration at all, so even a corrected caller would leak buffers.

## Per-symbol mismatch table (as found)

| symbol | declared in `service/extern.spl` | implemented in `net_uds.rs` | verdict |
|---|---|---|---|
| `rt_unix_socket_connect` | `(path: text) -> i64` | `(path_ptr: i64, path_len: i64) -> i64` :227 | MISMATCH (arity + shape) |
| `rt_unix_socket_listen` | `(path: text, backlog: i32) -> i64` | `(path_ptr: i64, path_len: i64, backlog: i32) -> i64` :71 | MISMATCH (arity + shape) |
| `rt_unix_socket_accept` | `(fd: i64) -> i64` | `(fd: i64) -> i64` :97 | **MATCH** |
| `rt_unix_socket_send` | `(fd: i64, data: text) -> i64` | `(fd: i64, data_ptr: i64, data_len: i64) -> i64` :122 | MISMATCH (arity + shape) |
| `rt_unix_socket_recv` | `(fd: i64, max_bytes: i64) -> text` | `(fd: i64, max_len: i64, out_len: *mut i64) -> i64` :148 | MISMATCH (arity, out-param, return) |
| `rt_unix_socket_free_buf` | *(not declared)* | `(ptr: i64, len: i64)` :193 | MISSING declaration |
| `rt_unix_socket_close` | `(fd: i64) -> i32` | `(fd: i64) -> i32` :203 | **MATCH** |

Two further `.spl` sites carried the same broken 1-arg `connect`
declaration and were equally dead:
`src/lib/nogc_sync_mut/qemu/qmp_client.spl:14` and
`src/app/simple_process_manager/transport/spm_transport_host.spl:15`.

## The real root cause: two implementations, one set of names

There are **two** independent implementations behind these seven names:

1. `src/compiler_rust/runtime/src/value/net_uds.rs` — the native runtime,
   `(ptr, len)` + out-param, with `rt_unix_socket_free_buf`.
2. `src/compiler_rust/compiler/src/interpreter_extern/qmp_socket.rs` —
   interpreter shims registered by name in `interpreter_extern/mod.rs:2149-2154`,
   which (before this fix) were **text-shaped** and arity-checked for the
   text shape.

The declarations matched lane 2 and not lane 1. The deployed seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, 2026-08-26 01:16) predates
lane 2: `strings` finds **zero** occurrences of any `qmp_socket.rs` error
message (e.g. `rt_unix_socket_listen requires 2 arguments`) while all seven
`rt_unix_socket_*` symbol names are present. So every `.spl` call fell
through to lane 1 and hit the ptr/len ABI. That is the -22 and the core
dump.

Fixing only one lane would have made the other regress on the next seed
redeploy, so **both** were converged on the ptr/len shape.

## Fix (chosen direction: `.spl` follows the native ptr/len ABI)

The native runtime is the real implementation, has the working `accept`,
and ships the `free_buf` companion — the ptr/len design is clearly the
intended one, and it is what the deployed binary actually executes. The
interpreter shims were the outlier.

`.spl` side (takes effect with **no build** — the stdlib is read as source
every run):

- `src/lib/nogc_sync_mut/service/extern.spl` — rewritten. Raw externs now
  declare the exact `(ptr, len)` / out-param ABI, `rt_unix_socket_free_buf`
  is declared, and a text-shaped wrapper layer
  (`uds_connect` / `uds_listen` / `uds_accept` / `uds_send` / `uds_recv` /
  `uds_close`) is exported so callers never touch pointers. Text is bridged
  to a raw pointer with `rt_string_data`, the received buffer is lifted back
  with `rt_string_new` and then released with `rt_unix_socket_free_buf`; the
  8-byte `out_len` slot comes from `rt_alloc`, is read with
  `rt_ptr_read_i64` and released with `rt_free`.
- `src/lib/nogc_sync_mut/qemu/qmp_client.spl` and
  `src/app/simple_process_manager/transport/spm_transport_host.spl` — the
  `connect` extern reshaped to `(path_ptr, path_len)`; the marshalling sits
  inside the existing `_qmp_sffi_connect` / `_spm_sffi_connect` seam, so no
  caller changed.

Rust side (reconciliation only — takes effect on the next seed rebuild,
and is what keeps this fix from regressing then):

- `interpreter_extern/qmp_socket.rs` — `connect`, `listen`, `send` and
  `recv` reshaped to the same `(ptr, len)` / out-param ABI; a
  `rt_unix_socket_free_buf` shim added and registered in
  `interpreter_extern/mod.rs`. The shims keep their own `CONNS` table (it is
  shared with `rt_fd_write` / `rt_fd_read_until` / `rt_fd_close`, which
  `qmp_client.spl` uses), so they were reshaped rather than deleted.
- Contract tests updated to the new arity, and extended to assert that a
  null path pointer yields `EINVAL` instead of being dereferenced and that a
  null `out_len` is refused.
- `cargo check --release --bin simple` passes (exit 0, 0 errors).

## Evidence — real UDS round trip

Two processes, one socket in a temp dir, driven through the deployed
`bin/simple`, using the exact wrapper bodies that ship in `extern.spl`.
Both directions carry real bytes.

```
$ ./bin/simple run tmpuds/ship_srv.spl &   # then, after 5s:
$ ./bin/simple run tmpuds/ship_cli.spl

CLI connect fd=4
CLI send bytes=7
CLI recv=[pong<ping-42>]

--- SERVER ---
SRV listen fd=4
SRV accept fd=5
SRV recv=[ping-42]
SRV send bytes=13
```

`listen` binds (fd 4, socket file created), `accept` returns a client fd,
the client's 7 bytes `ping-42` arrive intact at the server, and the
server's 13-byte reply `pong<ping-42>` arrives intact at the client. No
crash, no `-22`.

The same programs written against the **pre-fix** text-shaped declarations
produce, on the same binary:

```
SRV listen=-22
CLI connect=-22
```

## Residual gap — the interpreter lane still needs a seed rebuild

The round trip above runs on the JIT/native lane. When a module is demoted
to the interpreter, the ptr/len externs are unusable on the **deployed**
seed, because that binary has no ptr/len-shaped shims registered
(`SRV listen fd=-22`). The Rust reconciliation above fixes exactly this,
but only once a seed is rebuilt and redeployed.

A second, pre-existing and unrelated defect makes that lane easy to hit:
importing the wrappers across a module boundary demotes the whole module —
`[jit-fallback] unresolved external symbol 'uds_listen': whole module
dropped to the interpreter`. This is a cross-module JIT symbol-resolution
limitation, not part of this ABI defect, and `@always_inline` does not
avoid it. Until a seed redeploy lands, a consumer that needs the native
lane must keep the wrapper bodies in its own module.

## Can SCV E-09 adopt UDS now?

**Not yet, and it was deliberately left alone** (`src/lib/scv/editor_ipc.spl`
is untouched; its filesystem-pipe transport still stands). The ABI is fixed
and proven, but E-09 imports its transport across a module boundary, which
lands it on the interpreter lane — the one gap above. E-09 can adopt UDS
once a rebuilt seed is deployed; that redeploy is the single remaining
precondition.

## Ratchet

`sh scripts/check/check-unbacked-extern-ratchet.shs` FAILs on this tree,
but pre-existing and unrelated: none of the 35 newly-unbacked or 392 stale
symbols it names is one this change touched (no `rt_unix_socket_*`, no
`rt_string_data` / `rt_alloc` / `rt_free` / `rt_string_new` /
`rt_ptr_read_i64`).

Verified by delta, not by inspection: the same guard was run on a pristine
worktree of the same commit (`f2e10076977`) and the two offender sets are
**byte-identical** (432 names each, `comm` reports nothing on either side).
Both runs emit the same verdict line:

```
selftest: 4/4 fixtures OK
FAIL — 1384 symbol(s) checked, 35 newly unbacked: cosmos_fsbl_mmio_read32 ...
  ..., 392 baselined symbol(s) no longer unbacked (stale baseline): ...
```

This change therefore adds **no** new unbacked extern and removes none.

## Note on `.len()`

The wrappers pass `path.len()` / `msg.len()` as the byte length. Confirmed
that `.len()` on `text` is a **byte** count, not a character count:
`"aé★c".len()` returns 7 (1+2+3+1), not 4. Multibyte payloads are therefore
sent whole rather than silently truncated.
