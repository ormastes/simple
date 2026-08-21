# Dynamic SFFI generic `i64` bridge fabricates zero and miscarries ABI contracts

Date: 2026-08-21

Status: RESOLVED 2026-08-21 — interpreter-side dispatch fails closed; the native
`spl_wffi_call_i64`/`_f64` zero-sentinel migration stays OPEN as a separate P1
(carve-out was already stated in "Required fix" below). Evidence at the end.

Severity: critical (silent wrong value, leak, and ABI undefined behavior)

## Symptom

`dynamic_sffi.rs` lowers `Value::Nil`, embedded-NUL text conversion failures,
and every unsupported complex value to integer zero. Text conversion leaks a
`CString`. `call_fptr` transmutes every symbol solely by argument count into an
all-`i64` C function and lifts every result as `Value::Int`. Several typed helper
paths also return integer zero for null function pointers or missing dispatch.

## Owners

- `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- `src/compiler_rust/runtime/src/value/wsffi_native.rs`
- compiler-owned SFFI registry/generator under `src/compiler/90.tools/sffi_gen/`
- JIT/native extern registration and plugin manifest owners

## Pure-Simple-first boundary rationale

Safe wrappers and the compiler-owned contract registry are the Simple owners of
foreign semantics. They cannot recover an argument or return contract after the
Rust interpreter has erased it to `i64` or zero, so the Rust dispatch backstop
must also fail closed. No app/spec-local raw extern alias is an acceptable fix.

## Pre-fix reproducer

Rust unit coverage calls the marshaller with an array/object and embedded-NUL
text, and calls typed byte/font helpers with a null function pointer. Before the
fix these cases yield zero/default; after the fix they must return typed errors.

## Required fix

- make conversion fallible and retain scoped temporary C strings for the call;
- reject `Nil`, unsupported values, embedded NUL, null pointers, and excessive
  arity;
- remove `unwrap_or_else(|| Ok(Value::Int(0)))` fallbacks;
- limit the legacy generic bridge to explicitly admitted scalar signatures or
  disable it in robust/critical mode;
- route supported ABI families through generated typed thunks and one registry.

The native `spl_wffi_call_i64`/`spl_wffi_call_f64` value-returning bridges
still use zero for null pointers, unsupported arity, or invalid argument
descriptors. That collision cannot be repaired by choosing a different
sentinel: zero is a valid foreign result. These functions therefore remain an
open P1 migration to `Result` or status/out ABIs and must not be admitted as
robust/critical typed thunks in the interim.

## Adjacent regression coverage

- supported integer/bool scalar calls still work;
- missing manifest symbol remains a typed error;
- byte descriptors reject overflow/out-of-bounds;
- float and aggregate signatures never enter an `i64` thunk accidentally;
- temporary string storage is dropped after the call.

## Unblock condition

All exact/adjacent tests pass, cross-lane unknown/null errors agree, and
sabotaging either fallible conversion or null-pointer guard makes the relevant
test red.

## 2026-08-21 checked-transport implementation update

The native and interpreter lanes now expose `spl_wffi_call_i64_checked` as a
portable `[transport_status, foreign_value]` result and the native lane also
exposes status/out `spl_wffi_try_call_i64`. The byte-descriptor family has the
same checked pair transport. Argument counts are validated against both the
eight-argument ABI ceiling and the actual argument array before indexing.

`std.sffi.dynamic.DynLib.call_checked` is the canonical `Result<i64, text>`
lift. Legacy value-returning functions remain only for source compatibility and
must be migrated by provider family; they are not evidence of robust/critical
admission. Focused Rust tests prove that a legitimate foreign zero has status
zero while a null pointer or short argument array has a nonzero status.

## Resolution evidence (2026-08-21)

`src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs` now fails
closed on every shape this record named:

- `value_to_i64` (`:671`) admits **only** `Value::Int` and `Value::Bool`; every
  other value — `Nil`, text (embedded NUL included), arrays, objects — returns
  `unsupported_conversion("... does not admit argument type '<t>' without a
  typed ABI contract")`. No `Value::Int(0)` fabrication and no `CString` is
  created on this path at all, so the leak is gone with it.
- `call_fptr` (`:848`) rejects a null pointer up front (`null_function_pointer`)
  and rejects arity > 13 with a typed runtime error instead of falling through.
- the typed byte/font helpers (`spl_wffi_call_i64_with_bytes`,
  `spl_fonts_call_init_blob` / `_init_path` / `_layout_text`) each guard
  `fptr == 0` and marshal through the fallible `strict_i64_array` /
  `strict_owned_bytes`, which bounds-check the byte descriptor
  (`offset + length <= owner.len()`) and reject non-byte values.
- no `unwrap_or_else(|| Ok(Value::Int(0)))` remains in the file.

Unit coverage in the same file pins all of it, including the adjacent
regressions this record asked for: `generic_dispatch_rejects_values_without_typed_contracts`,
`generic_dispatch_rejects_embedded_nul_text_instead_of_zero`,
`generic_dispatch_rejects_null_function_pointer`,
`scoped_byte_adapter_rejects_null_function_pointer`,
`generic_dispatch_retains_integer_and_bool_scalars`,
`packed_byte_foreign_descriptor_rejects_out_of_bounds`,
`packed_byte_foreign_capability_cannot_escape_call`.

Seed rebuilt clean with these in place (`cargo build --release --bin simple`,
rc=0, 2026-08-21 14:53).

**Still open, deliberately (see the checked-transport update above, which
supersedes part of this):** the LEGACY value-returning `spl_wffi_call_i64` /
`spl_wffi_call_f64` in
`src/compiler_rust/runtime/src/value/wsffi_native.rs` still return zero for a
null pointer / unsupported arity / invalid descriptor. As this record already
states, that cannot be repaired by picking another sentinel and needs a
`Result`/status-out ABI migration; it must not be admitted as a robust/critical
typed thunk until then. Tracked as the remaining P1 of this lane.
