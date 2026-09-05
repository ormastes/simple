# web_framework signing: digest does not match HMAC-SHA256, and CSRF tokens are NOT session-bound

- **Status:** OPEN — partially fixed; **3 spec examples are RED and left RED deliberately**
- **Date:** 2026-08-18
- **Severity:** High. CSRF tokens that do not vary by session are forgeable/
  transplantable between sessions.
- **Area:** `src/lib/nogc_sync_mut/web_framework/session.spl` (`compute_signature`),
  `src/lib/nogc_sync_mut/web_framework/csrf_integration.spl` (`csrf_token_for_session`)
- **Spec:** `test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl`

## What was fixed

Both functions previously had a hard type error (`hmac_sha256(...) -> text`
passed to a local `bytes_to_hex(bytes: [i64])`) and had therefore **never
executed** — see `never_compiled_code_sweep_2026-08-18.md`. They now execute:
8 of 11 examples pass, including 64-char output length, lowercase-hex charset,
determinism, sensitivity to the secret, and sensitivity to the data.

Dead helpers deleted from both files: the local `bytes_to_hex` and `hex_digit`
(each had exactly one caller — the broken line).

## What is still WRONG (the 3 red examples)

```
✗ compute_signature matches the openssl HMAC-SHA256 oracle
  expected 76e6d0e8d2475fc78a88f884145dd586abd43904408523306526b462f6b6934d
  got      00000019000000b500000093000000030000009a000000270000009f00000077
✗ csrf_token_for_session matches the openssl HMAC-SHA256 oracle
  expected 36129a1d3ec8f47c11d9006e31a7d1993f9f094eee4157518092f316461eeff5
  got      000000620000004c000000e8000000c8000000d7000000600000008b000000fc
✗ binds a CSRF token to its session id      (two different session ids -> SAME token)
```

The oracle is external, not self-consistency:
`printf '%s' "<data>" | openssl dgst -sha256 -hmac "<key>" -r`.

Two independent defects are visible here:

1. **The digest value is wrong**, and its SHAPE is diagnostic: eight groups of
   `000000xx`, i.e. each byte rendered in an 8-wide field. Only 8 values are
   represented where HMAC-SHA256 has 32 bytes.
2. **CSRF tokens are not bound to the session id** — `session_a` and
   `session_b` produce identical tokens. Any token would be valid for any
   session. (String interpolation itself is fine: a standalone probe confirmed
   `"csrf:{sid}"` -> `csrf:session_a`.)

## The part that is not explained, stated plainly

The wrong value is **byte-identical across three different implementations of
the function body**:

1. `hmac_sha256(secret, data)` (returns hex text directly)
2. `bytes_to_hex(hmac_sha256_bytes(text_to_bytes(secret), text_to_bytes(data)))`
3. `_webfw_digest_to_hex(hmac_sha256_bytes(...))` with a uniquely-named local
   hex helper

The file on disk was verified to contain edit 3 (`session.spl:707`). Identical
output from three different bodies means the executed code is not the code on
disk, or the call is not reaching this function at all. That is unresolved.

Two ambiguity hazards were investigated and are real, but neither explains the
invariance, so neither should be recorded as the cause:

- `hmac_sha256(key: text, data: text) -> text` has **three** definitions with
  the same name and signature: `common/crypto/hmac.spl:12` (pure Simple, the
  correct one), `nogc_sync_mut/io/crypto_sffi.spl:96`, and
  `app/io/crypto_ffi.spl:96`. Test runs already warn that co-compiled same-name
  definitions can mis-dispatch.
- `bytes_to_hex` has **ten** definitions under `src/lib`, including an
  **untyped** `pub fn bytes_to_hex(data)` at `common/serialization/__init__.spl:510`.

The pure-Simple crypto stack itself is CORRECT and was verified directly:
`hmac_sha256_bytes(text_to_bytes("k"), text_to_bytes("abc"))` then
`bytes_to_hex` yields
`342e519ce0ad6c03a36b98eeb3f1d130db4813b9df4d1160eda488d712dc78ee`, matching
openssl exactly. So the defect is in dispatch/reachability, not in HMAC.

A further pre-existing error blocks calling `compute_signature` from a
standalone program: `error: semantic: type mismatch: comparing string with
integer`, raised while loading `session.spl` — i.e. that module has at least
one more never-executed type error beyond the two fixed here.

## Why the spec is left RED rather than removed or weakened

The three failures are real defects on a security path. Deleting the examples
or relaxing them to self-consistency (`sig == sig`) would restore a green suite
while leaving forgeable CSRF tokens in place — precisely the failure mode that
let this code ship unexecuted for so long. Per the lane rule, a failing test is
not skipped without approval.

**Do not "fix" this by changing the expected values to the observed ones.** The
expected values are openssl's and are correct.
