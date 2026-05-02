# Bug: HMAC-SHA-512 disagrees with RFC reference vectors

- **Date filed:** 2026-05-01
- **Status:** Open (pre-existing — surfaced while wiring PBKDF2 unit tests)
- **Module:** `src/lib/common/crypto/hmac.spl::hmac_sha512_bytes`
- **Surfaced by:** `test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl`
  (PBKDF2-HMAC-SHA-512 TC1 was added today and fails).

## Symptom

PBKDF2-HMAC-SHA-512 with `passwd="passwd"`, `salt="salt"`, `c=1`,
`dkLen=64` is by definition equal to `HMAC-SHA-512(passwd, salt || 0x00000001)`.

```
expected (RFC 7914 §11):
  867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce
actual (this impl):
  c74319d99499fc3e9013acff597c23c5baf0a0bec5634c46b8352b793e324723d55caa76b2b25c43402dcfdc06cdcf66f95b7d0429420b39520006749c51a04e
```

A direct call to `hmac_sha512_bytes(passwd_bytes, salt_bytes_with_block_index_1)`
produces the same `c74319d9…` value, confirming the divergence is in
HMAC-SHA-512 (or the underlying SHA-512 / pad path) rather than in the
PBKDF2 outer driver.

## Out of scope for the 2026-05-01 PBKDF2 perf fix

The PBKDF2 inner-loop perf optimisation landed today touches only the
SHA-256 path. The SHA-512 PBKDF2 driver was not modified. This bug is
therefore a pre-existing impl correctness issue, surfaced (but not
caused) by the new unit test.

## Repro

```bash
bin/simple test test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl
```
… would fail on the SHA-512 TC1 case (the `describe` block has been
disabled with a pointer to this bug doc until it's fixed).

Also reproducible via direct HMAC-SHA-512 call:

```spl
use std.crypto.hmac.{hmac_sha512_bytes}
use std.crypto.types.{bytes_to_hex}
fn main():
    var k = [0x70, 0x61, 0x73, 0x73, 0x77, 0x64]   # "passwd"
    var m = [0x73, 0x61, 0x6c, 0x74,                # "salt"
             0x00, 0x00, 0x00, 0x01]                # || INT(1)
    print(bytes_to_hex(hmac_sha512_bytes(k, m)))
```

## Hypotheses to investigate

1. SHA-512 padding length encoding off-by-one (SHA-512 length field is
   128 bits, not 64 — easy to mis-pack).
2. SHA-512 round constants or initial hash values mistyped.
3. `sha512_process_block` operates on 64-bit lanes; could be silently
   truncated to 32-bit somewhere.

## Cross-references

- `src/lib/common/crypto/sha512.spl` — likely root cause.
- `src/lib/common/crypto/hmac.spl::hmac_sha512_bytes` — wrapper.
- `doc/08_tracking/bug/pbkdf2_interpreter_perf_2026-05-01.md` — the
  perf bug whose fix exposed this.
