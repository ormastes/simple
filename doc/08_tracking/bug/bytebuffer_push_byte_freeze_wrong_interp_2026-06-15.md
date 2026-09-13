# Bug: ByteBuffer.push_byte(v) + freeze() yields wrong byte values in interpreter

## Closed 2026-09-13 — Does not reproduce: pushed bytes survive `freeze()` exactly

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the entry's minimal repro — `ByteBuffer.new()`, `push_byte` of `0xde 0xad 0xbe 0xef`, then `freeze()` — gives `len=4` and reads back `222 173 190 239`, i.e. exactly `0xde 0xad 0xbe 0xef`. No garbage values.
- **inferred**: the original driver was `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`, a Linux artifact not present here, so this is "does not reproduce on the current Windows seed" rather than a located fix.
- Note found in the same run and filed against its own entry, not this one: `for b in span:` over the frozen `ByteSpan` still iterates zero times — see `for_in_custom_struct_no_iterator_protocol_2026-06-15.md`, which remains OPEN. The byte VALUES are correct; only iteration is missing.

**ID:** bytebuffer_push_byte_freeze_wrong_interp_2026-06-15
**Filed:** 2026-06-15
**Status:** CLOSED 2026-09-13 (does not reproduce). **Severity:** P1 — silent data corruption; produces wrong bytes with no error
**Component:** interpreter / src/lib/common/bytes/span.spl `ByteBuffer.push_byte`
**Driver:** `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`

## Summary

`ByteBuffer.push_byte(v: i64)` accumulates bytes and `ByteBuffer.freeze()` is
supposed to return a `ByteSpan` over those bytes. In the interpreter, the bytes
returned by `freeze()` are wrong — garbage values instead of the pushed values.

## Minimal repro

```simple
use std.common.bytes.span.{ByteSpan, ByteBuffer}

fn main():
    var buf = ByteBuffer.new()
    buf.push_byte(0xde)
    buf.push_byte(0xad)
    buf.push_byte(0xbe)
    buf.push_byte(0xef)
    val span = buf.freeze()
    print("len=" + span.len().to_text())
    print("get(0)=" + span.get(0).to_i64().to_text())
    print("get(1)=" + span.get(1).to_i64().to_text())
    print("get(2)=" + span.get(2).to_i64().to_text())
    print("get(3)=" + span.get(3).to_i64().to_text())
```

Run from project root:
```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
bin/simple run <above_file>
```

## Observed output

```
len=4
get(0)=240
get(1)=6
get(2)=0
get(3)=0
```

## Expected output

```
len=4
get(0)=222     # 0xde
get(1)=173     # 0xad
get(2)=190     # 0xbe
get(3)=239     # 0xef
```

## Notes

- `span.len()` is correct (4).
- `push_u8(v: u8)` (not tested here) may behave differently.
- The issue appears to be in how `push_byte(v: i64)` stores the i64 value into the
  `[u8]` buffer internally, or how `freeze()` reads it back.
- The spec harness `describe/it` path may exhibit different behaviour (see
  `cross_module_struct_method_poisons_itblock_byte_ops_2026-06-15.md`).

## Workaround

Accumulate bytes as `[u8]` array directly and push via `.push(v.to_u8())`:

```simple
var arr: [u8] = []
arr.push(0xdeu8)
arr.push(0xadu8)
arr.push(0xbeu8)
arr.push(0xefu8)
val span = ByteSpan.new(arr)
```

This is the pattern used in `ctypes.spl`'s `_hex_to_bytes` helper (see comment in
that file). Confirmed working.
