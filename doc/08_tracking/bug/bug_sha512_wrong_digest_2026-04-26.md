# SHA-512 implementation produces wrong digest

Date: 2026-04-26
Source: discovered while fixing crypto_reference_spec `method get not found` failures
Spec: `test/unit/lib/crypto/crypto_reference_spec.spl`

## Symptoms

`std.crypto.sha512.sha512_bytes([])` returns
`6fac5aa1e616d70854d0d5b7cb8caf5f8c49b69c24b88403dd6b0985dff59c3b32dbb6e350c0f4d2a1243894bacf9cf43e4ed52ffb23cb66aa927414d5e10302`

Expected (FIPS 180-4):
`cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e`

Cascades to: `hmac_sha512`, `pbkdf2_sha512` — all produce wrong bytes.

## Reproduce

```spl
use std.crypto.sha512.{sha512_bytes}
use std.crypto.types.{bytes_to_hex}

fn main():
    val r = sha512_bytes([])
    print(bytes_to_hex(r))
```

## Spec test that fails

`test/unit/lib/crypto/crypto_reference_spec.spl :: PBKDF2 reference vectors :: matches PBKDF2-HMAC-SHA512 reference vector`

Reaches the assertion stage and produces an incorrect digest, not a symbol-resolution error.

## Likely location

`src/lib/common/crypto/sha512.spl` — possibly initial-hash constants, K constants,
sigma functions, or 64-bit big-endian byte assembly. SHA-256 (`sha256_bytes`) appears
correct (PBKDF2-HMAC-SHA256 test passes against the published vector).

## Out of scope for the spec-fix worktree

Detected after fixing `text.get` -> slice in `crypto/types.spl` and adding
`use` resolution in `pbkdf2.spl` and `hmac.spl`. The algorithmic correction
should land in its own change.
