# Bug: `rt_unix_socket_*` extern shape mismatch (.spl text ABI vs Rust ptr/len ABI)

- **Date:** 2026-08-26
- **Found by:** Wave-4 SCV lane A (E-09 editor IPC transport bring-up)
- **Status:** OPEN — E-09 works around it with a pipe-spool transport

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

## Fix direction
Either rewrite the `.spl` externs to the (ptr,len)/out-param shape with a
text wrapper layer (declaring `rt_unix_socket_free_buf`), or add
text-shaped runtime entry points. Until then no `.spl` caller may use this
surface; SCV editor IPC (E-09) uses a pipe-spool transport instead.
