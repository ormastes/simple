# Bug: interpreter "Function 'str.bytes' not found"

**ID:** interpreter_str_bytes_missing_2026-06-12
**Severity:** P2
**Status:** open (workaround in place)
**Date:** 2026-06-12

## Symptom

Calling `std.common.base_encoding.base64.base64_encode` (or `base64_decode`)
under `bin/simple run` (interpreter mode) crashes with:

    Function 'str.bytes' not found

Both `base64_encode` and `base64_decode` call `data.bytes()` on the input
`text` argument. The `.bytes()` method on `text`/`str` is not registered in
the interpreter's extern dispatch table, only in the compiled (native/SMF) path.

## Repro

    bin/simple run -e 'use std.common.base_encoding.base64.{base64_encode}; print(base64_encode("hello"))'

## Root Cause

`src/lib/common/base_encoding/base64.spl` line ~50: `val bytes = data.bytes()`
The interpreter extern registry does not include `str::bytes`; the method is
only available in compiled mode via the Rust runtime.

## Workaround

`src/lib/common/ui/html_ui/payload.spl` now provides `_interp_base64_encode`
and `_interp_base64_decode` — pure-Simple implementations that use `char_at`
and codepoint arithmetic to derive UTF-8 bytes without calling `.bytes()`.
`payload_encode`/`payload_decode` delegate to these safe implementations.
The round-trip is verified for ASCII, brace/quote/newline chars, and non-ASCII
UTF-8 codepoints (multi-byte).

## Fix Needed

Register `str::bytes` (returning `[u8]`) in the interpreter extern dispatch
table, mirroring how `char_at` and `length` are already registered.
File: `src/compiler/` interpreter extern dispatch (search for `char_at` registration).
