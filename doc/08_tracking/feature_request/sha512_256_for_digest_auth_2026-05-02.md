# FR: SHA-512/256 for HTTP Digest Auth (RFC 7616)

**Date:** 2026-05-02
**Status:** Open
**Blocks:** `src/lib/nogc_sync_mut/http/auth/digest.spl` algorithm=SHA-512-256 paths

## Problem

RFC 7616 §6.4 lists three mandatory digest algorithms: MD5, SHA-256, and SHA-512-256.
SHA-512-256 is **not** a truncated SHA-512. It is SHA-512 with different initial hash
values (FIPS 180-4 §5.3.6.2) and produces a 256-bit (32-byte) digest.

The current crypto library (`src/lib/common/crypto/sha512.spl`) implements SHA-512
with its standard IVs only. There is no SHA-512/256 function.

`_digest_hash` in `digest.spl` returns `""` for algorithm="SHA-512-256" and the
`http_digest_make_response` / `http_digest_verify` callers propagate the empty
string as a sentinel (no panic, no silent wrong answer).

## Required Change

Add `sha512_256_bytes(bytes: list) -> list` to `src/lib/common/crypto/sha512.spl`
(or a new `sha512_256.spl` module) using the FIPS 180-4 §5.3.6.2 initial values:

```
H0 = 0x22312194FC2BF72C
H1 = 0x9F555FA3C84C64C2
H2 = 0x2393B86B6F53B151
H3 = 0x963877195940EABD
H4 = 0x96283EE2A88EFFE3
H5 = 0xBE5E1E2553863992
H6 = 0x2B0199FC2C85B8AA
H7 = 0x0EB72DDC81C52CA2
```

Then wire it into `_digest_hash` in `digest.spl` and add a KAT in `digest_spec.spl`.

## Reference

- FIPS 180-4 §5.3.6.2 (SHA-512/256 initial hash values)
- RFC 7616 §6.4 (algorithm registry)
- `src/lib/nogc_sync_mut/http/auth/digest.spl` — `_digest_hash` function
