# Native C runtime has no `spl_wffi_call_i64_with_bytes` — llm_caret native build fails closed (2026-11-16)

Status: verification-pending. Severity P1 (blocks every native llm_caret build at the release tip).

## Symptom
At `origin/release/1.0.0` `f85a20b44ad`, Windows, seed `seed-vtable.exe`:

```
native-build src/app/llm_caret/main.spl -o build/nb/llm_caret.exe
Build failed: 1 internal Simple symbol(s) have no implementation and would be fabricated as weak stubs returning the tagged-nil sentinel 3: spl_wffi_call_i64_with_bytes
```

## Root cause
The byte-descriptor WFFI facade (PBL-03, 2026-08-14) was implemented in the Rust
runtime (`runtime/src/value/wsffi_native.rs`) and the interpreter
(`interpreter_extern/dynamic_sffi.rs`) but never in the C runtime
(`src/runtime/runtime_native.c`), which is what native builds link. Its
Simple callers (`chrome_render_module_sffi.spl`, `chromium_reference_oracle_sffi.spl`,
`hip_compute.spl`, `model_executor/backend.spl`, `dynlib_provider.spl`) are
reached by llm_caret's import closure.

## Fix
`spl_wffi_call_i64_with_bytes` and `spl_wffi_call_i64_with_bytes_checked` added to
`runtime_native.c` (+ `runtime.h`), mirroring the Rust semantics: null fptr,
negative/overflowing/out-of-bounds window -> rejected; at most 8 foreign args;
`length == 0` passes a NULL pointer; the unchecked form returns 0 on any non-OK.

## Evidence
Spec `test/03_system/runtime/wffi_call_i64_with_bytes_native_spec.spl`
(fixture `test/fixtures/wffi_with_bytes/main.spl`, real `strnlen` callee). RED/GREEN in the PR.

## Not covered
The remaining 55 `rt_*` link stubs in the llm_caret native build
(`rt_local_unix_*` 18, `rt_tls_*` 20, `rt_package_*` 10,
`rt_retained_private_credential_*` 6, `rt_dns_lookup`) are separate gaps.
