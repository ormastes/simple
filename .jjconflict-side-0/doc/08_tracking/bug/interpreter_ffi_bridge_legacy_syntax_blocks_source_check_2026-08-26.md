# Interpreter FFI bridge legacy syntax blocks source check

**Status:** Open compiler/source migration blocker  
**Observed:** 2026-08-26  
**Path:** `src/app/interpreter/ffi/bridge.spl`

## Evidence

The self-hosted entrypoint reports the bootstrap-seed warning and rejects the
unchanged beginning of this file before reaching the SFFI hardening edit:

```text
line 5: unexpected token `..` in `from ..core import ...`
line 14: unexpected token `:` in the Rust-like struct field declaration
24 parser errors total
```

The same lines are present in `origin/main`; the hardening change only removes
the dead private block beginning after `NativeValue`.  The package initializer
checks successfully, and the optimizer can analyze the bridge, but neither is
a substitute for a clean direct source check.

## Required fix

Migrate the surviving typed native registry and value bridge to canonical
Simple syntax, preserving its public `call_native`, `register_native`, and
`NativeFunction` API and adding focused SPipe coverage.  Do not restore the
deleted generic all-`u64` dynload dispatcher as a workaround.

## Performance constraint

Preserve average O(1) registry lookup.  Do not add per-call library lookup,
symbol lookup, signature parsing, generic marshalling, or extra value copies.
