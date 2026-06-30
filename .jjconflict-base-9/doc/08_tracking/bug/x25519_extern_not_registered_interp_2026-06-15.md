# Note: rt_tls13_x25519 bare extern unregistered — pure fallback runs in test mode

**ID:** x25519_extern_not_registered_interp_2026-06-15
**Date:** 2026-06-15
**Severity:** P3 — cosmetic / dead-code extern declaration; no runtime impact on test runner

## Summary

`src/lib/nogc_async_mut_noalloc/tls/x25519.spl` declares:

```
extern fn rt_tls13_x25519(scalar: [u8], u_coord: [u8]) -> [u8]
```

This extern is NOT registered in the interpreter's SFFI dispatch table
(`src/compiler_rust/compiler/src/interpreter_extern/`).  The registered
externs use different names:
- `rt_tls13_x25519_public_key`
- `rt_tls13_x25519_shared_secret`

(registered in `runtime_symbols.rs` lines 1045–1046, used in `ssh_session_kex.spl`).

## Actual behaviour

**X25519 IS pure under the test runner.**  Because `rt_tls13_x25519` is
unregistered, the `if fast.len()==32` fast-path guard inside `x25519.spl`
always fails (the extern call returns an empty/error result), and the
pure-Simple Montgomery-ladder fallback executes.  KAT values
(RFC 7748 §5.2 and §6.1) match exactly under `bin/simple test` — verified
13/13 PASS at 76 s under `SIMPLE_BOOTSTRAP_DRIVER=seed`.

**Only `bin/simple run` is affected.**  Run-mode is strict about unknown
externs and raises "unknown extern function: rt_tls13_x25519" if
`x25519_typed` is called directly from a standalone script.

## Impact

- `x25519_typed` and `x25519_typed_pubkey` run **pure** under the interpreter
  test runner (Montgomery-ladder fallback) and produce correct KAT outputs.
- KAT asserts in `asym_spec.spl` ARE executed under the seed interpreter.
- `bin/simple run` on a script that calls x25519_typed directly will crash
  with "unknown extern function: rt_tls13_x25519".

## Fix Options

1. Register `rt_tls13_x25519` in `interpreter_extern/tls13.rs` using the
   existing `ring` X25519 implementation — eliminates the dead extern.
2. Rename `x25519.spl`'s extern to match the registered names
   (`rt_tls13_x25519_shared_secret` / `rt_tls13_x25519_public_key`).
3. Remove the fast-path extern entirely from `x25519.spl` if it is never
   registered anywhere and the pure fallback is acceptable.
