# `std.crypto.poly1305` does not export `poly1305_key_gen` (RFC 8439 §2.6.2)

- **Date:** 2026-07-20
- **Area:** `src/lib/common/crypto/poly1305.spl`
- **Severity:** medium (missing function, not a wrong-value bug; blocks 2 of
  9 examples).
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/poly1305_spec.spl --no-session-daemon
```

```
✗ poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key
    semantic: function `poly1305_key_gen` not found
✗ poly1305_key_gen always returns exactly 32 bytes
    semantic: function `poly1305_key_gen` not found
```

2 examples, 2 failures in this describe block; 7 other examples in the file
(poly1305_mac correctness) pass (Passed: 7, Failed: 2 overall).

## Root-cause hypothesis

`test/unit/lib/crypto/poly1305_spec.spl:19` imports
`use std.crypto.poly1305.{poly1305_mac, poly1305_key_gen}`. `poly1305_mac`
resolves fine. `poly1305_key_gen` — the RFC 8439 §2.6.2 helper that derives
a one-time Poly1305 key from a ChaCha20 key + nonce via the ChaCha20 block
function — is not defined anywhere:

```
grep -rn "fn.*key_gen" src/lib/common/crypto/*.spl src/os/crypto/*.spl
```

returns nothing for poly1305. Both `src/lib/common/crypto/poly1305.spl` and
its `src/os/crypto/poly1305.spl` mirror only define `poly1305_init`,
`poly1305_block`, `poly1305_finalize`, `poly1305_mac` — no key-derivation
helper. This is a genuinely missing implementation, not a rename: the
function has never existed under any name in this module.

## What NOT to do

Do not remove/soften the two `it` blocks — `poly1305_key_gen` is a real,
separately-testable RFC 8439 primitive and its absence is a real gap in the
`std.crypto.poly1305` public surface, not a stale test.

## Affected specs

- `test/unit/lib/crypto/poly1305_spec.spl` (2 of 9 examples)
