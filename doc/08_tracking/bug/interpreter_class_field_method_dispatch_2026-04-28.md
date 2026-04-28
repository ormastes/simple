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

This rules out the local-binding hypothesis; the interpreter's type-tracking discards the `[u8]` typing somewhere between class-field access and method-dispatch resolution.

## Root cause hypothesis (not confirmed)

The interpreter's static type-checker probably uses the runtime tag of the field's stored RuntimeValue rather than the declared field type. Since heap pointers in this runtime are tagged in a way that looks like `i64` to the dispatcher, the check fails.

This is **separate from but related to** the enum-field-i64-zero-destructure compile-mode bug. Both stem from incomplete static-type-info propagation through field-access expressions, but they manifest differently:
- Compile-mode enum: silently zeroes the value.
- Interpreter class: rejects the method call at semantic check.

## Workaround

None known. The test failures are blocking but reproducibly localized to the interpreter's class-field method-dispatch path. Native-mode test runner has its own wrapper-parser bug per memory `feedback_sspec_compile_pipeline.md`, so we can't run these specs in compile mode either.

## Why root-cause fix matters

- Blocks interpreter-mode testing of any pure-Simple module that returns user-defined classes containing `[u8]` or array fields.
- TLS AC-6 regression suite cannot be fully validated until either this is fixed or a working native-mode test path lands.

## Investigation pointers

- Look at the interpreter's static type-checker — specifically the field-access path that resolves `obj.field_name` types.
- Compare interpreter handling of class field access vs let-bound local bindings.
- Memory `feedback_compile_mode_false_greens.md` (2026-04-25) and `feedback_interpreter_test_limits.md` describe related interpreter quirks; this is another instance of the same family.
