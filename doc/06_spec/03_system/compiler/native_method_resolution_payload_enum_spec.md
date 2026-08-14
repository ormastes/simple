# Native method-resolution payload enum regression

Executable source:
`test/03_system/compiler/native_method_resolution_payload_enum_spec.spl`

Requirement: `REQ-BST-ENUM-001`

This fail-closed system test invokes the real native compiler once with stub
fallback disabled and rejects the Rust bootstrap seed. It retains the compiler
and candidate logs below
`build/test-artifacts/native_method_resolution_payload_enum/`.

## Operator steps

1. **Compile and execute all method-resolution payload variants.** Require all
   five adjacent enum shapes and the explicit native PASS verdict.
2. **Exercise a static factory call shaped like BackendError.type_error.**
   Require correct static-owner recovery.
3. **Exercise push on an initially empty inferred array.** Require the native
   receiver and pushed value to remain intact.
4. **Compile inferred module constants without reclassifying folded payloads.**
   Require inferred integer, float, boolean, text, and folded binary values.
5. **Require a real native candidate and an explicit probe verdict.** Missing
   compiler, seed identity, compile failure, execution failure, or absent
   marker is a test failure.

Run after an admitted Stage 4 compiler exists:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test \
  test/03_system/compiler/native_method_resolution_payload_enum_spec.spl \
  --mode=interpreter
```

Current restart12 status: BLOCKED because the final Stage 3 cycle exited 139
before producing the Stage 4 test authority. This manual is reviewed source
documentation; canonical `spipe-docgen` regeneration remains required after
unblock and must preserve the visible steps above.

