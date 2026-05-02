# Bug: HMAC-SHA-512 disagrees with RFC reference vectors

- **Date filed:** 2026-05-01
- **Status: FIXED 2026-05-01 — root cause: bug-doc typo (compared `"passwd"` impl output against the reference vector for `"password"`); HMAC-SHA-512 / SHA-512 implementations verified correct against draft-josefsson-pbkdf2-test-vectors-00 §3 and Python `hashlib.pbkdf2_hmac("sha512", ...)`.**
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

## Resolution (2026-05-01)

The "expected" value in the **Symptom** section (`867f70cf…0a57fce`) is
the PBKDF2-HMAC-SHA-512 reference output for `password="password"`
(8 bytes, draft-josefsson-pbkdf2-test-vectors-00 §3 TC1), NOT for
`password="passwd"` (6 bytes) as written. The Simple HMAC-SHA-512 impl
in fact produces `c74319d9…51a04e` for `("passwd", "salt"||0x00000001)`,
which matches Python `hmac.new(b"passwd", b"salt"+b"\x00\x00\x00\x01",
hashlib.sha512).hexdigest()` exactly.

There is no SHA-512 / HMAC / PBKDF2 implementation defect. The bug
report was a test-vector typo: a 6-byte password was paired with the
reference value for the 8-byte password.

Confirming evidence:

1. `test/unit/lib/crypto/crypto_reference_spec.spl` already exercises
   `pbkdf2_sha512("password", "salt", 1) → 867f70cf…0a57fce` and PASSES
   in interpreter mode (re-verified 2026-05-01 with cache invalidated).
2. `test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl` now adds
   three PBKDF2-HMAC-SHA-512 byte-input vectors:
   - TC1 `("password","salt",1,64) → 867f70cf…0a57fce`
   - TC2 `("password","salt",2,64) → e1d9c16a…f27ccf4e`
   - long-key `(200×'A',"salt",1,64) → d4d976cd…eabe9429` (forces the
     `key_bytes.len() > block_size → sha512_bytes(key)` branch in
     `hmac_sha512_bytes` that the short-key reference vector does not
     reach).
   All three PASS in interpreter mode and match Python
   `hashlib.pbkdf2_hmac("sha512", …)` byte-exact.

Note on RFC numbering: the original bug doc cites "RFC 7914 §11" as the
source of the SHA-512 vector. RFC 7914 §11 only specifies PBKDF2-HMAC-
SHA-**256** vectors (used internally by scrypt); there is no SHA-512
PBKDF2 vector in RFC 7914. The de-facto SHA-512 reference vectors come
from `draft-josefsson-pbkdf2-test-vectors-00 §3`, which is the source
the new spec cites.
