# Bug: extern calls taking `[u8]` reject a genuinely-typed `[u8]` array — "byte array element must be integer, got u8"

**Date:** 2026-07-04
**Severity:** P1 — every extern that marshals bytes through
`native_io_helpers::extract_bytes` (send/write paths across TCP, UDP, file
I/O) silently only works when the caller passes an untyped/`[i64]` integer
array, and rejects the natural, statically-typed `[u8]` value real code
produces (e.g. any `wire.spl`-style `ByteWriter.to_bytes()` codec output)
**Status:** Open — worked around at the call site in
`src/lib/nogc_sync_mut/game_net/udp_transport.spl`; no interpreter fix yet

## Summary

`extract_bytes` (`src/compiler_rust/compiler/src/native_io_helpers.rs:133`)
converts an extern argument to `Vec<u8>` by matching each array element:

```rust
Value::Int(i) => bytes.push(*i as u8),
_ => return Err(... "byte array element must be integer, got {type_name}" ...)
```

It only accepts `Value::Int` elements. A Simple-level array whose static
type is genuinely `[u8]` (built from `u8`-suffixed literals, or returned by
a function declared `-> [u8]`, e.g. `wire.spl`'s `encode_input_frame`)
apparently boxes its elements as a distinct `Value::U8` variant at the
interpreter's runtime-value layer, not `Value::Int` — so it is rejected with
`byte array element must be integer, got u8`, even though the extern's
declared Simple-level parameter type is `[u8]` and the call type-checks.

Extern calls that use `extract_bytes` include (at minimum) `native_udp_send`,
`native_udp_send_to`, and the analogous TCP/file write helpers built on the
same helper — any of them fail identically when handed a real `[u8]` value.

## Reproduction

```simple
use std.nogc_sync_mut.game_net.wire.{InputFrame, encode_input_frame}

extern fn native_udp_bind(addr: text) -> (i64, i64)
extern fn native_udp_send_to(fd: i64, data: [u8], data_len: i64, addr: text) -> (i64, i64)

fn main():
    val (hdl, _err) = native_udp_bind("127.0.0.1:39851")
    val data = encode_input_frame(InputFrame(seq: 1u32, tick: 2u32, move_x: 0.5, move_y: 0.25))
    val n: i64 = data.len()
    val (_sent, _serr) = native_udp_send_to(hdl, data, n, "127.0.0.1:39852")
```

Fails: `error: semantic: byte array element must be integer, got u8`.

Replacing `data` (the `[u8]` value) with an untyped int-literal array
(`[1, 2, 3]`) or an explicit `[i64]` local built by looping
`plain.push(data[i].to_i64())` succeeds — same extern, same declared `[u8]`
parameter type, only the runtime element tag of the actual argument differs.

## Why this matters beyond the obvious

`src/lib/nogc_async_mut/io/quic/quic_udp_socket.spl`'s doc comment claims
these interpreter ABIs are "Verified" — but its own `send_to(data: [u8], ...)`
method forwards a real `[u8]` value straight into `native_udp_send_to`
unconverted, which this bug shows fails the moment `data` actually holds
`Value::U8`-boxed bytes (e.g. from any codec producing typed `[u8]`, not
literal ints). The verification evidently covered the wire shape/ABI, not an
end-to-end call with a genuinely `[u8]`-typed payload.

## Workaround applied

`src/lib/nogc_sync_mut/game_net/udp_transport.spl`'s `UdpTransport.send`
re-boxes the payload through a plain `[i64]` local (looping
`plain.push(payload[i].to_i64())`) before calling `native_udp_send_to`. This
is a call-site workaround, not a fix — every other caller that hands a real
`[u8]` value to an `extract_bytes`-backed extern hits the same wall.

## Real fix needed

`extract_bytes` should also accept whatever runtime tag a genuinely `[u8]`-
typed Simple array actually uses (`Value::U8`, if that is the boxed
representation) alongside `Value::Int`, so callers do not need to manually
downgrade a typed byte array to an untyped integer array before any
byte-taking extern call.
