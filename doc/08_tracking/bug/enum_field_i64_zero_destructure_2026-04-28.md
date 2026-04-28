# Bug: enum field destructuring drops i64 values (returns 0)

**Date:** 2026-04-28
**Severity:** correctness — silently drops integer fields when destructuring enum variants
**Discovered by:** TLS live-lane bisection (`/dev tls_live_bug_fix_restart`, D4/D9/D10 fix attempt)

## Symptom

In compile-mode (Cranelift bare-metal `x86_64-unknown-none`), constructing an enum variant with an integer field and then destructuring it loses the field's value.

```
enum RecordResult:
    Ok(content_type: i64, data: [u8])
    Err(msg: text)

# Inside _record_unpack_inner_with_len:
val real_content_type: i64 = _u8_at(inner, cursor).to_i64()
serial_println("inside: real_ct={real_content_type}")  # prints 22
RecordResult.Ok(real_content_type, data)               # construct

# At test site:
if val RecordResult.Ok(ct, dt) = res:
    # ct reads as 0, but inner unpack proved real_ct=22
```

Same behavior with named-field construction (`Ok(content_type: ..., data: ...)`) and with `u8` field type. The `text` field of `Err(msg: text)` works correctly — only integer fields are affected.

## Reproduction

Verified empirically via `[BISECT-UNPACK]` probe in `_record_unpack_inner_with_len`:

```
[BISECT-UNPACK] inner_len=6 cursor=5 real_ct=22
[DBG] D4 ct4=0 dt4.len()=5
```

inner unpack has `real_ct=22` (= 0x16, the encoded TLS content type), but the test's `ct4` after destructuring is 0. The `data` field (a `[u8]`) destructures correctly — `dt4.len()=5` and the bytes are right.

## Root cause hypothesis (not confirmed)

Likely an i64-vs-tagged-int representation mismatch in the enum variant's field storage. The runtime probably tags integer values in slot positions, and the unbox/extract path during destructuring might be reading a NIL_VALUE-like tag (which is 3) and returning 0, OR shifting the raw int through a tag-sensitive path that maps the value to 0 for small-magnitude integers.

The `text` field works because it's a heap pointer and the tag scheme treats heap-pointer slots correctly.

## Workaround in tree (2026-04-28)

For the TLS record-decrypt path, added a parallel API `rt_tls13_record_decrypt_compact` (C extern in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`) that returns the content_type as byte[0] of a `[u8]` runtime array, with the data bytes following. Test code calls this directly via `rt_bytes_u8_at(res, 0)` to read content_type instead of going through the enum.

`src/os/tls13/record13.spl` keeps the `RecordResult` enum for hosted-mode and for callers that don't need the integer field. The `i64` field type was a probe — `u8` had the same bug.

## Why root-cause fix matters

Any compile-mode code path that returns integer payloads through enum variants silently zeroes the integer. This is broad:
- `Result<T, E>` style enums with integer payloads
- Status-code enums
- AEAD/crypto Result types
- Any error enum carrying an error code

The workaround pattern (compact `[u8]` with sentinel byte) doesn't generalize cleanly to multi-field structures.

## Investigation pointers

- Look at how enum variants with integer fields lower in `src/compiler_rust/compiler/src/mir/lower/lowering_*.rs`
- Compare with `text` field handling (which works) to find where integer fields diverge
- `MirInst::EnumNew` (or whatever the enum-construction MirInst is) and how it stores field values
- The matching destructuring path in `lowering_expr_match.rs` or similar
