# Dynamic SFFI generic `i64` bridge fabricates zero and miscarries ABI contracts

Date: 2026-08-21

Status: CLAIMED — `/root`, SFFI v2 hardening lane

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
