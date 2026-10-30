# Cross-target link has no runtime/entry for non-host targets (2026-10-26)

**Date:** 2026-10-26
**Status:** open
**Evidence:** `C:/dev/hircfg-probe/logs/`, `C:/dev/hircfg-probe/summary.txt`
**Compiler:** `build/s2hw/stage2.exe`, run as `native-build --source src --entry src/hello.spl --target <triple> --cache-dir C:/dev/hircfg-probe/cache --emit-object`
**Severity:** P2

## Symptom

`logs/i686-w64-mingw32.link.log`:

```
worker error: error: LLVM native linking failed: host C runtime/entry compilation unsupported: target 'i686-w64-mingw32' on host 'x86_64-windows'
error: LLVM native linking failed: host C runtime/entry compilation unsupported: target 'i686-w64-mingw32' on host 'x86_64-windows'
```

A manual llvm-mingw link of the emitted i686 `.o` fails with undefined
`_rt_string_new_literal` and other runtime symbols (reported by the
coordinator; not captured in the logs directory). There is no runtime
compiled/provided per cross target, so only the host-matching target can link.

## Not a bug (recorded to avoid re-triage)

The x86_64-msvc `rt_transient_array_scope_state_v1` undefined-symbol failure
was a stale runtime copy. The symbol is defined at
`src/runtime/runtime_native.c:1866` on release/1.0.0.

## Suspected area

`src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl` (host C
runtime/entry compilation gate). Cross targets need a target-triple-driven
runtime build (clang/lld only; never GCC).
