# X25519 unregistered bare extern removed

**ID:** x25519_extern_not_registered_interp_2026-06-15
**Date:** 2026-06-15
**Severity:** P3 — dead unimplemented optimization path; standalone interpreter failure
**Status:** Source fixed 2026-07-15; existing KAT and standalone run verification pending

## Summary

`src/lib/nogc_async_mut_noalloc/tls/x25519.spl` declared:

```
extern fn rt_tls13_x25519(scalar: [u8], u_coord: [u8]) -> [u8]
```

This extern was not implemented or registered in the interpreter's SFFI
dispatch table (`src/compiler_rust/compiler/src/interpreter_extern/`). Related
runtime manifest symbols use different names:
- `rt_tls13_x25519_public_key`
- `rt_tls13_x25519_shared_secret`

(listed in `runtime_symbols.rs` and used separately by `ssh_session_kex.spl`).

## Historical behaviour

The unimplemented extern was called before the pure-Simple Montgomery ladder.
Interpreter modes did not share a reliable unknown-extern fallback contract,
so standalone run mode could fail before reaching the ladder.

The existing typed-wrapper spec contains RFC 7748 §5.2 and §6.1 assertions,
but those assertions have not been rerun for the current source change.

## Resolution

- Removed the `rt_tls13_x25519` declaration and its unconditional fast-path
  call.
- Reused the existing pure-Simple Montgomery ladder as the sole implementation.
- Kept the existing RFC 7748 KAT assertions; no new test framework or fixture
  was added.

## Verification remaining

- Run `test/01_unit/lib/common/crypto/typed/asym_spec.spl` and record the RFC
  KAT result.
- Run a standalone interpreter path through the existing typed wrapper and
  confirm that no unknown-extern diagnostic occurs.
- No runtime PASS is claimed by this source-only update.
