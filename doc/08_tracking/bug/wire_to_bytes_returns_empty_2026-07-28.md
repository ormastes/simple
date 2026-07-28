# `wire_to_bytes()` returns an empty array on both engines

**Date:** 2026-07-28
**Status:** Open
**Severity:** High — silently corrupts every TLS 1.2 length field
**Area:** `src/lib/nogc_async_mut/io/tls_common.spl`, stdlib `to_bytes`

## Symptom

```
fn wire_to_bytes(wire: text) -> [i64]:
    to_bytes(wire)
```

returns `[]` for every input, on the interpreter (test runner) *and* under
`bin/simple run`. Measured 2026-07-28 with a probe importing
`std.nogc_async_mut.io.tls_common`:

| expression | expected | actual |
|---|---|---|
| `len(wire_to_bytes("h2"))` | 2 | 0 |
| `len(wire_to_bytes(bytes_to_wire([104, 50])))` | 2 | 0 |
| `len(wire_to_bytes(encode_u8(2)))` | 1 | 0 |
| `len(wire_to_bytes(encode_u16_be(9)))` | 2 | 0 |

The inverse direction is fine: `bytes_to_wire([104, 50])` correctly yields
`"h2"`, and that direction is spec-covered by
`test/01_unit/lib/nogc_async_mut/io/tls_common_wire_guard_spec.spl`. Only the
text -> bytes direction is broken, and it has no spec.

## Impact

`wire_to_bytes` is the length primitive for the whole async TLS 1.2 stack —
about 20 call sites across `io/tls.spl`, `io/tls_io.spl` and
`io/tls_handshake.spl`, including record-header lengths
(`tls_io.spl:161,166`), Certificate body lengths
(`tls_handshake.spl:410,414`), the pre-master secret
(`tls_handshake.spl:206`) and Finished ciphertext length
(`tls_handshake.spl:304`). Every one of those computes 0 today, so any
handshake driven through this path emits zero-length fields.

This was not caught earlier because the async TLS 1.2 server handshake has no
unit spec — the failure is silent (wrong bytes, no error).

## Repro

Any spec that imports `std.nogc_async_mut.io.tls_common` and asserts
`len(wire_to_bytes("h2")) == 2`.

## Workaround in use

`len(text)` already gives the byte count for wire text (the established idiom —
see `tls_common_hooks.spl`, which passes `len(key)` to `rt_wire_to_hex`).
`build_alpn_extension_block` in `io/tls_handshake.spl` uses `len(protocol)` for
exactly this reason; the comment there points back at this file.

## Fix

Root-cause `to_bytes` on `text` (builtin resolution or wire-text decoding), add
a `wire_to_bytes` case to `tls_common_wire_guard_spec.spl` covering the
text -> bytes direction, then sweep the ~20 call sites above.
