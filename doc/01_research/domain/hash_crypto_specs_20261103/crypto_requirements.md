# Cryptographic specification requirements

Status: requirements draft, not conformance certification or executed evidence.
Source hashes and pinned editions: [sources.md](sources.md). Section locators are
normative anchors; PDF page numbers below are physical file pages where stated.
RFC TXT uses its printed `[Page N]` markers. Existing tests are inventory candidates,
not verification receipts. Every owner/backend needs its own execution evidence.

| ID | Official source section | Test obligation |
|---|---|---|
| REQ-CRYPTO-AES-001 | FIPS 197-upd1 5.1–5.3, Appendices A/B | AES-128 and AES-256 independent encryption/decryption KATs and expanded keys; assert 10 versus 14 rounds via correct outputs, including AES-256 key-expansion special case. Appendix B is a cipher example; do not mislabel arbitrary generated vectors as Appendix B. |
| REQ-CRYPTO-GCM-001 | SP 800-38D 6.2–6.5 and 7.1 | AES-128/256 authenticated encryption with independent ciphertext/tag: empty plaintext/AAD; 1/15/16/17-byte boundaries; 96-bit IV fast path and non-96-bit IV GHASH path if exposed. |
| REQ-CRYPTO-GCM-002 | SP 800-38D 5.2.1, 7.2 | Exact successful plaintext; independently mutate ciphertext, tag, AAD, nonce and key; authentication failure must not release unauthenticated plaintext. Validate supported IV/tag lengths through API contract. |
| REQ-CRYPTO-GCM-003 | SP 800-38D 8, Appendix C | Enforce actual nonce-uniqueness/length policy and supported tag policy at the responsible caller; reject counter/length exhaustion using bounded fixtures or owner injection, not huge allocations. A unit KAT cannot establish operational nonce uniqueness. |
| REQ-CRYPTO-CHACHA-001 | RFC 8439 2.1.1, 2.2.1, 2.3.2, 2.4.2 | Published quarter-round/block/encryption vectors; counter, little-endian encoding and 63/64/65-byte boundaries. |
| REQ-CRYPTO-CHACHA-002 | RFC 8439 2.5.2, 2.8.1–2.8.2, Appendix A | Poly1305 and AEAD exact ciphertext/tag; AAD/ciphertext pad-to-16 and length encoding with 0/1/15/16/17 bytes; modified inputs rejected with no plaintext release. Preserve 256-bit key and 96-bit nonce contract. |
| REQ-CRYPTO-ECDH-001 | RFC 7748 5, 5.2, 6.1–6.2 | X25519/X448 only where exported: published scalar/u-coordinate and Alice/Bob shared-secret vectors; scalar decoding, input mask, noncanonical u-coordinate handling. RFC 7748 does not specify P-256 ECDH. |
| REQ-CRYPTO-ECDH-002 | RFC 7748 6–7; RFC 8446 4.2.8.2 | TLS X25519/X448 caller MUST reject all-zero shared secret. RFC 7748 standalone primitive permits the check; do not convert its MAY into a universal primitive MUST. Malformed encoding/key-share length uses the caller contract. |
| REQ-CRYPTO-SIGN-001 | FIPS 186-5 section 5 (RSA), section 6 (ECDSA) | Independent positive signatures plus wrong message/key, out-of-range r/s, malformed encoding and invalid key; identify exact hash, key parameters and encoding. RSA encoding needs its referenced PKCS #1 standard; FIPS 186-5 alone is not an encoded-signature vector corpus. |
| REQ-CRYPTO-TLS-001 | RFC 8446 4.2.3, 4.2.8, 4.4.3, 5.2–5.3, 7.1 | Production handshake/record callers: negotiated supported group/signature/AEAD, transcript-bound CertificateVerify, key schedule and per-record nonce; reject unsupported negotiation, tampering and sequence exhaustion. Primitive KATs do not prove handshake correctness. |

PDF page navigation: BLAKE3 has matching printed/physical numbers; NIST front
matter shifts physical numbers, so section locators above are authoritative.
Private extractions explicitly label each physical PDF page for reproducibility.
Do not copy equations from extraction without checking glyphs against the PDF.

Existing candidate inventory (read coverage and assertions before mapping):

- `test/01_unit/lib/crypto/p256_ecdh_nist_cdh_kat_spec.spl`: P-256 separate source required.
- `test/01_unit/lib/crypto/ecdsa_p256_spec.spl` and RSA PSS/PKCS1 specs in the same directory.
- `test/01_unit/os/crypto/chacha20_poly1305_spec.spl`.
- `test/01_unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl`.
- `test/01_unit/os/tls13/chacha20_poly1305_cipher_suite_spec.spl`.

Open source obligations: source exact AES/GCM independent KAT corpora; acquire
P-256 domain/key-agreement guidance (SP 800-186 and SP 800-56A as applicable),
and PKCS #1/RFC 8017 when RSA encoding is exercised. Review current errata before
claiming full standard conformance. These missing references do not prevent
authoring bounded tests grounded in the sources already pinned.
