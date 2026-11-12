# str.byte_len / char_at not found in nested call context (seed interpreter)

- id: str_byte_len_not_found_in_nested_call_context_2026-11-12
- status: verification-pending
- component: seed interpreter (`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`)
- found by: diag-P5 lane (`fix_transaction.spl` apply_to_body, text_len_of shapes)

## Symptom
`self.text_of().byte_len()` (str method on a method-call result receiver) failed with
`semantic: method 'byte_len' not found on value of type str in nested call context`.
Hoisting the receiver into a `val` worked.

## Root cause
Chained receivers go through `call_method_on_value` in `method_dispatch.rs`, which carries
its own subset of str methods. `byte_len` and `char_at`/`at` were present in the
direct-receiver arm (`interpreter_method/string.rs`) but missing from the chained arm.

## Fix
Added `byte_len` (UTF-8 byte count) and `char_at`/`at` (char-indexed, empty on
out-of-range) to the chained str arm, matching `interpreter_method/string.rs`.

## Repro / prevention
`test/01_unit/compiler/interpreter/str_method_nested_call_arg_spec.spl` — byte_len,
len, trim, char_at nested as arguments and chained on method-call receivers, each
compared with the hoisted form.

## Open follow-up (not fixed here)
On "héllo" (6 bytes, 5 chars) the seed produced "héll" for a chained
`s.trim().substring(0, 5)` inside an `expect(...)` argument, but "héllo" for a direct
`t.substring(0, 5)`. That suggests a byte-vs-char index split between substring
dispatch paths. It needs its own repro; the spec here uses ASCII for the `len` case.
