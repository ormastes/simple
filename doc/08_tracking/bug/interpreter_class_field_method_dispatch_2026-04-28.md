# Bug: interpreter type-checker can't resolve method dispatch on class fields

**Date:** 2026-04-28
**Severity:** test-infrastructure — blocks interpreter-mode tests of class-returning functions
**Discovered by:** TLS AC-6 regression-suite check after live-gate green (`/dev tls_live_bug_fix_restart`)

## Symptom

In **interpreter mode**, the static type-checker fails to resolve method dispatch (`.len()`, `.push()`, etc.) when the receiver is a class field accessed via `obj.field`. The runtime value is correct (a heap pointer to the typed array), but the dispatcher reports `i64` and rejects the method call.

Three failing tests in `test/system/os_tls_client_auth_spec.spl`:

```
✗ parses CertificateRequest signature_algorithms
    semantic: method `len` not found on type `i64` (receiver value: 135362697510257)
✗ builds an empty client Certificate message
    semantic: method `push` not found on type `i64` (receiver value: 135362682142593)
✗ builds a non-empty client CertificateVerify message
    semantic: method `push` not found on type `i64` (receiver value: 135362698494993)
```

The "receiver value" is a heap pointer (high bits 0x7B+ confirm it's in heap-region range).

## Reproduction

In `test/system/os_tls_client_auth_spec.spl:30`:

```
val req = parse_certificate_request(body)  # returns CertificateRequest13
expect(req.request_context.len()).to_equal(0)
```

`CertificateRequest13.request_context` is declared as `[u8]` in the class definition at `src/os/tls13/handshake13.spl:80`. The interpreter's static type-checker still rejects `.len()` on `req.request_context`.

Workaround attempt — explicit local with type annotation — does not help:

```
val ctx: [u8] = req.request_context
expect(ctx.len()).to_equal(0)  # still fails
```

## Root Cause (CONFIRMED)

**The extern `rt_array_new_with_cap` is missing from the interpreter's extern handler table.**

### Call chain

1. `parse_certificate_request` in `src/os/tls13/handshake13.spl` calls `_byte_buf(0)` (line 18)
2. `_byte_buf` calls `extern fn rt_array_new_with_cap(cap: i64) -> [u8]` (line 13)
3. The interpreter extern handler table in `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` has `rt_array_new` mapped to `ffi_array::rt_array_new_fn`, but **has no entry for `rt_array_new_with_cap`**
4. Falls through to `dynamic_ffi::try_call_dynamic` in `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs`
5. `dynamic_ffi` calls the native runtime function via dlsym and returns `Value::Int(heap_ptr)` — the raw native pointer cast to `i64` — because it has no return-type information at dispatch time (see lines 616–621: `fn i64_to_value(v: i64) -> Value { Value::Int(v) }`)
6. This `Value::Int(heap_ptr)` is stored as the `request_context` field of `CertificateRequest13`, and is also stored as the local byte-buffer variables inside `build_certificate_bytes` and `build_certificate_verify_bytes`
7. When `.len()` or `.push()` is called on the receiver, `evaluate_method_call` in `src/compiler_rust/compiler/src/interpreter_method/mod.rs` calls `recv_val.type_name()` which returns `"i64"` for `Value::Int` — no array method match is found — error is emitted

### Why all three tests fail (not just test 1)

- **Test 1** (`req.request_context.len()`): fails via FieldAccess path in `interpreter/expr/calls.rs` — a `Value::Int` is loaded from `fields["request_context"]` and dispatched into `evaluate_method_call_with_self_update`
- **Test 2** (`build_certificate_bytes`): fails inside the function body on a **local variable** `buf` (created by `_byte_buf(0)` inline) — no FieldAccess involved
- **Test 3** (`build_certificate_verify_bytes`): same pattern as test 2

Tests 2 and 3 cannot be fixed by patching the FieldAccess dispatch path in `interpreter/`. The local variable `buf: [u8]` is bound to a `Value::Int` from the start; the method dispatcher in `interpreter_method/mod.rs` fails before any FieldAccess resolution occurs.

### Relevant file locations

| File | Role |
|------|------|
| `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` | Extern handler table — missing `rt_array_new_with_cap` |
| `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs:616-621` | Returns `Value::Int` unconditionally for unknown externs |
| `src/compiler_rust/compiler/src/interpreter_extern/ffi_array.rs` | Has `rt_array_new_fn` — already handles same args as `rt_array_new_with_cap` |
| `src/compiler_rust/compiler/src/interpreter_method/mod.rs` | Method dispatch — `Value::Int` hits no array branch → error |
| `src/os/tls13/handshake13.spl:13,18` | Declares and calls `rt_array_new_with_cap` |

## Proposed Fix (REJECTED — see "Actual root cause" below)

~~**In `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`**, add `rt_array_new_with_cap` to the handler table alongside `rt_array_new`~~

This was tried (`mod.rs:1287-1292` adds `"rt_array_new_with_cap" => ffi_array::rt_array_new_fn(&evaluated)`) but did NOT fix the tests. **`rt_array_new_fn` itself returns `Value::Int(rv.to_raw() as i64)` at line 31 of `ffi_array.rs`, not `Value::Array`.** So routing `rt_array_new_with_cap` to the same handler doesn't help — the handler already returns a raw-pointer-as-Int and the method dispatcher rejects it.

## Actual root cause (deeper)

The FFI extern handler convention in `interpreter_extern/ffi_array.rs` returns array RuntimeValues as `Value::Int(rv.to_raw() as i64)` (raw pointer cast to i64). This is "OK" within the FFI layer because subsequent FFI calls (`rt_array_push`, `rt_array_get`, etc.) accept the raw pointer as their first arg. **But when the value crosses back into Simple-land for native method dispatch (`.len()`, `.push()`), the dispatcher in `interpreter_method/mod.rs` sees `Value::Int` and rejects all array methods.**

For Simple-language method dispatch on the result of an extern, the FFI return needs to be wrapped as `Value::Array(...)` (or whatever native shape the receiver type implies) using the declared return type from the `extern fn ... -> [u8]` signature.

### Where the fix should go

Either:
1. **In `dynamic_ffi.rs:616-621`** — when calling an unknown extern with a declared `[u8]` (or generic `[T]`) return type, wrap the raw i64 pointer as `Value::Array` using the runtime's `RuntimeArray` shape. Requires plumbing the declared return type through to the FFI dispatcher.
2. **In `ffi_array.rs:31`** — change `rt_array_new_fn` to return `Value::Array(rv_to_array(rv))` and audit all FFI consumers (`rt_array_push_fn`, `rt_array_get_fn`, etc.) to unwrap properly. More invasive but cleaner long-term.
3. **In `interpreter_method/mod.rs`** — special-case `Value::Int` receivers when the static type info from the AST/HIR shows the expression should be `[u8]`. Adds heuristic at the dispatch site rather than the source.

Option (1) is most surgical. Option (2) is most principled but touches more code. Option (3) is fragile but maybe simplest.

## Scope constraint on original investigation

This root cause is in `src/compiler_rust/compiler/src/interpreter_extern/` (outside the `interpreter/` sub-directory scope of the original task). A partial fix limited to `interpreter/expr/calls.rs` (FieldAccess coercion using class-def type info) would only resolve test 1 and would leave tests 2 and 3 broken. The correct fix is the missing extern handler entry above.

## Workaround

None known. The test failures are blocking but reproducibly localized to the interpreter's class-field method-dispatch path. Native-mode test runner has its own wrapper-parser bug per memory `feedback_sspec_compile_pipeline.md`, so we can't run these specs in compile mode either.

## Why root-cause fix matters

- Blocks interpreter-mode testing of any pure-Simple module that returns user-defined classes containing `[u8]` or array fields.
- TLS AC-6 regression suite cannot be fully validated until either this is fixed or a working native-mode test path lands.

## Investigation pointers (superseded)

~~Look at the interpreter's static type-checker — specifically the field-access path that resolves `obj.field_name` types.~~

Root cause is confirmed upstream: `rt_array_new_with_cap` has no interpreter extern handler, so dynamic FFI returns a raw `Value::Int` pointer instead of `Value::Array`. Fix the extern table first.
