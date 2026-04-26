# SHA-512 implementation produces wrong digest

Date: 2026-04-26
Status: **Fixed 2026-04-26**
Source: discovered while fixing crypto_reference_spec `method get not found` failures
Spec: `test/unit/lib/crypto/crypto_reference_spec.spl`

## Symptoms

`std.crypto.sha512.sha512_bytes([])` returned
`6fac5aa1e616d70854d0d5b7cb8caf5f8c49b69c24b88403dd6b0985dff59c3b32dbb6e350c0f4d2a1243894bacf9cf43e4ed52ffb23cb66aa927414d5e10302`

Expected (FIPS 180-4):
`cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e`

Cascaded to: `hmac_sha512`, `pbkdf2_sha512` — all produced wrong bytes.

## Reproduce

```spl
use std.crypto.sha512.{sha512_bytes}
use std.crypto.types.{bytes_to_hex}

fn main():
    val r = sha512_bytes([])
    print(bytes_to_hex(r))
```

## Spec test that failed

`test/unit/lib/crypto/crypto_reference_spec.spl :: PBKDF2 reference vectors :: matches PBKDF2-HMAC-SHA512 reference vector`

Reached the assertion stage and produced an incorrect digest, not a
symbol-resolution error.

## Root cause

`src/lib/common/crypto/types.spl` — `rotr64` and `shr64` used Simple's bare
`>>` operator on `i64`, which is **arithmetic** (sign-extending). Empirical
verification: `0x8000000000000000 >> 1` yields `-4611686018427387904`
(=`0xC000000000000000`), not the expected `0x4000000000000000`.

For SHA-512, both the round constants `K[0..79]` and several initial hash
values `H[0..7]` have bit 63 set, so the message-schedule σ-functions
(`σ0`, `σ1`) and round Σ-functions (`Σ0`, `Σ1`) silently smeared sign bits
into upper positions on every right shift / right rotate, corrupting every
digest from the first compression step onward.

The 32-bit siblings (`rotr32`, `shr32`) were correct because they explicitly
masked with `0xFFFFFFFF`; the asymmetry was the smoking gun.

## Fix

`src/lib/common/crypto/types.spl`: rewrote `rotr64` and `shr64` to perform
one logical shift (clear the sign bit propagated by `>>` after a shift of
1) and then complete the remaining `n - 1` shifts arithmetically — all of
which are now non-negative and therefore behave logically. `n == 0` is
guarded explicitly. SHA-512 sigma rotations use n in {1, 6, 7, 8, 14, 18,
19, 28, 34, 39, 41, 61}; none reach 64, so `x << (64 - n)` in `rotr64`
stays well-defined.

## Verification

- `sha512_bytes([])` → matches FIPS 180-4 KAT (`cf83e1357eefb8bd...da3e`).
- `sha512_bytes([0x61, 0x62, 0x63])` ("abc") → matches FIPS 180-4
  Appendix C.1 (`ddaf35a193617aba...f23a`).
- 56-byte FIPS Appendix C.2 vector matches.
- `crypto_reference_spec :: PBKDF2-HMAC-SHA512 reference vector` → PASS.
- Deliberate-fail probe: reverting only the shift fix re-broke the
  PBKDF2-HMAC-SHA512 vector; restoring re-greened it.
