# `chacha20_poly1305_seal`/`_open` raw-`[u8]` API expected by specs doesn't exist (two incompatible implementations exist instead)

- **Date:** 2026-07-20
- **Area:** `src/lib/common/crypto/chacha20_poly1305.spl`,
  `src/lib/common/crypto/typed/aead.spl`
- **Severity:** medium (blocks all examples that call seal/open in both
  affected specs).
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/chacha20_poly1305_spec.spl --no-session-daemon
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/chacha20_poly1305_wycheproof_spec.spl --no-session-daemon
```

```
✗ seal produces canonical §2.8.2 ciphertext byte-exact
    semantic: function `chacha20_poly1305_seal` not found
✗ open(seal(pt)) recovers original plaintext
    semantic: function `chacha20_poly1305_seal` not found
✗ open with canonical ct+tag recovers plaintext
    semantic: function `chacha20_poly1305_open` not found
```
(and equivalently for every `seal`/`open` call site in both spec files).

## Root-cause hypothesis

Both specs import
`use std.crypto.chacha20_poly1305.{chacha20_poly1305_seal, chacha20_poly1305_open}`
and call them with **raw `[u8]` arrays**, expecting a **tuple** return, e.g.:

```
val (ct, tag) = chacha20_poly1305_seal(_key_2_8_2(), _nonce_2_8_2(), _aad_2_8_2(), _pt_2_8_2())
```
(argument order: key, nonce, aad, pt).

Two implementations exist in the tree, and **neither** matches this shape:

1. `src/lib/common/crypto/chacha20_poly1305.spl` (the module the import path
   actually resolves to) defines `chacha20_poly1305_encrypt`/`_decrypt`
   (raw `[u8]` in/out) — different names, not `_seal`/`_open`.
2. `src/lib/common/crypto/typed/aead.spl:131,154` defines
   `chacha20_poly1305_seal(key: SecretKey, nonce: Nonce, pt: Plaintext, aad: ByteSpan) -> AeadSealed`
   / `chacha20_poly1305_open(...)` — the right *names*, but (a) wrapped
   typed-newtype parameters (`SecretKey`/`Nonce`/`Plaintext`/`ByteSpan`) that
   don't accept plain `[u8]`, (b) a struct return (`AeadSealed`) not a tuple,
   and (c) **different argument order** (`pt` before `aad`, vs. the spec's
   `aad` before `pt`).

So there is no function anywhere in the tree with the raw-array,
tuple-returning, (key, nonce, aad, pt)-ordered `chacha20_poly1305_seal`/
`_open` signature both specs are written against. This is not a simple
dead-import-path fix (unlike `sha256_x4_spec.spl`, where the correctly-named
function existed verbatim in a sibling file) — the required function
genuinely does not exist under any name/signature combination.

## What NOT to do

Do not repoint the import at `std.crypto.typed.aead` and reorder/rewrap the
call-site arguments to match — that would be writing new adapter behavior
into the test, which risks silently exercising different semantics than the
spec's own RFC 7539 §2.8.2 comments describe. This needs an implementation
decision (add a raw-array seal/open wrapper, or rewrite the specs to the
typed API) from whoever owns the AEAD surface.

## Affected specs

- `test/unit/lib/crypto/chacha20_poly1305_spec.spl` (all examples)
- `test/unit/lib/crypto/chacha20_poly1305_wycheproof_spec.spl` (all examples)
