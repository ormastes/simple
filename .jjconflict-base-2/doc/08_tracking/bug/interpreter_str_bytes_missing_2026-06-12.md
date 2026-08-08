# Bug: interpreter "Function 'str.bytes' not found"

**ID:** interpreter_str_bytes_missing_2026-06-12
**Severity:** P2
**Status:** FIXED 2026-06-13 (JIT/AOT `.bytes()`/`.chars()` added). Original
interpreter symptom no longer reproduces (interpreter already handles `bytes`).
**Date:** 2026-06-12

## Fix landed (2026-06-13)

The doc was stale/inverted: the interpreter ALREADY handles `bytes`
(`interpreter_method/string.rs:28`) and prints correctly. The live gap was the
**JIT/native** path — `.bytes()` (and `.chars()`) were not mapped, so compiled
code hit `Runtime error: Function 'str.bytes' not found`. Added runtime fns
`rt_string_bytes` / `rt_string_chars` (`runtime/src/value/collections.rs`,
modeled on `rt_string_split`) returning an int-array / string-array, and wired
them at the same sites `rt_string_split` uses: `runtime/src/value/mod.rs`
re-export, `codegen/runtime_sffi.rs` RuntimeFuncSpec, `common/runtime_symbols.rs`
RUNTIME_SYMBOL_NAMES, the cranelift method maps (`codegen/instr/calls.rs`,
`closures_structs.rs`), and `method_registry/builtins.rs`. Verified in
JIT/AOT/interp: `"Hi".bytes()` → `[72, 105]`, `"Hi".chars()` → `["H","i"]`;
base_encoding specs 21/1 unchanged (1 pre-existing failure, identical on the
pre-fix seed). LLVM-backend method maps are a sibling parity follow-up (default
path is cranelift).

**Note — a SEPARATE bug surfaced via base64:** `base64_encode` still returns
empty in JIT, but NOT because of `.bytes()` (that now works). Root cause:
**a string method on a local/global string VARIABLE returns empty in JIT** — the
receiver is folded into the call name instead of loaded. Minimal repro
`val T = "ABCDEF"` then `T.char_at(0)` → empty, `T.length()` → -1 (interpreter
`A`/`6`); also a module-level `val TABLE: text`. NOT global-init and NOT
module-specific (local vals fail too); params (`s: text`) and literals work.
Tracked in `jit_string_method_on_var_receiver_folds_2026-06-13.md` (distinct
from `stage4_imported_const_compare`).

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
