# ChaCha20-Poly1305 Tag Bug Finding — 2026-04-17

## Summary

The pure-Simple implementation at `src/os/crypto/chacha20_poly1305.spl`
produces a **Poly1305 authentication tag that diverges from the RFC 8439 §2.8.2
canonical test vector** for a 114-byte plaintext. Ciphertext (first 114 bytes)
matches byte-for-byte; the last 16 bytes (tag) do not. Python `cryptography`
41.0.7, Node `node:crypto` 22.22, and (by transitive agreement) OpenSSL all
produce the RFC-correct tag.

## Evidence

Running `test/system/chacha_poly_roundtrip_spec.spl` (new):

```
✗ pure-Simple encrypt produces the canonical ciphertext||tag
    expected ...11ae10b594f09e26a7e902ecbd0600691
    got      ...11ae10b598d9dea6ad1cd2ecb62610691
✓ python encrypt matches the canonical ciphertext||tag
✓ node encrypt matches the canonical ciphertext||tag
```

Cipher prefix (114 bytes): identical.
Tag (last 16 bytes): diverges.

## Why existing specs missed it

`test/system/os_crypto_ref_primitives_spec.spl` asserts only:
- `out.len() == 130` (114 cipher + 16 tag)
- `out[0] == 0xd3`, `out[1] == 0x1a`, `out[2] == 0x8d`, `out[3] == 0x34`

It never compares the tag bytes. The 114-byte RFC vector also does not appear
in `crypto_input_matrix(block_size: 64)`, which only covers the set
`{0, 1, 3, 4, 63, 64, 65, 192}`. The bug appears to be length-dependent.

## Hypothesis

`src/os/crypto/chacha20_poly1305.spl::_build_mac_data` constructs
`AAD || pad16(AAD) || CT || pad16(CT) || len(AAD) || len(CT)` as required by
RFC 8439. For the RFC vector: AAD=12 bytes (pad=4), CT=114 bytes (pad=14).
The 14-byte pad is a plausible bug site — matrix inputs sit at pad sizes
`{0, 1, 12, 13, 15}` but never 14.

Next step: instrument `_build_mac_data` for CT=114 and compare the 144-byte
MAC input to a known-good reference (e.g. Python `cryptography` internals or a
hand-traced RFC worked example).

## Cross-vendor agreement on everything else

| Property | Status |
|---|---|
| ChaCha20 stream (no MAC) | green — `os_crypto_ref_primitives_spec.spl` asserts byte-exact RFC 7539 §2.4.2 |
| Poly1305 MAC alone | green — same spec asserts RFC 7539 §2.5.2 |
| RFC 8439 §2.8.2 ciphertext bytes [0..3] | green |
| RFC 8439 §2.8.2 full ciphertext (114 bytes) | green |
| **RFC 8439 §2.8.2 tag (16 bytes)** | **RED** |
| Python ↔ Node roundtrip over 8-input matrix | green |
| Python ↔ Node RFC 8439 full output | green |

## Suggested Lane Assignment

Lane 2 (Symmetric-AEAD) in
`doc/03_plan/agent_tasks/pure_simple_crypto_tls_remains_2026-04-16.md`. Add an
acceptance test that matches the full 130-byte RFC 8439 output (not just the
first 4 ciphertext bytes) to prevent regression.

## Second finding: tag comparison on the decrypt side

The same spec's negative-path test also fails:

```
✗ pure-Simple decrypt rejects a zeroed tag
```

`chacha20_poly1305_decrypt` accepts a 16-byte all-zero tag for the 114-byte
RFC plaintext+AAD+key combination. For matrix inputs (lengths 0..192) the
pure-Simple decrypt correctly verifies vendor-produced tags — so the bug is
again length- or input-specific, not a categorical "tag ignored" problem.

This strongly suggests both issues share a single root cause in the MAC-input
assembly or Poly1305 evaluation at specific lengths. A zero tag happening to
match the computed (wrong) tag is the most parsimonious explanation — i.e.
for CT=114 the computed Poly1305 may collapse to all-zero under the buggy
path.

## Related Specs

- `test/system/chacha_poly_roundtrip_spec.spl` — reproduces both bugs and
  passes the surrounding cross-vendor lanes (11/13 green).
- `test/system/os_crypto_ref_primitives_spec.spl` — existing spec; assertion
  depth should be tightened to cover tag bytes.
