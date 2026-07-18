<!-- codex-research -->

# Research — Security / Crypto Algorithm & Protocol Catalog (custom-type-first)

Created 2026-06-15. One of three sibling catalogs added in the same wave:
- this doc (security/crypto)
- [`../search/search_pattern_match_catalog_2026-06-15.md`](../search/search_pattern_match_catalog_2026-06-15.md)
- [`../compress/compression_codec_catalog_2026-06-15.md`](../compress/compression_codec_catalog_2026-06-15.md)

Companion plan: [`doc/03_plan/lib/crypto/custom_type_alpha_crypto_team_plan_2026-06-15.md`](../../../03_plan/lib/crypto/custom_type_alpha_crypto_team_plan_2026-06-15.md).

This is the **broad external map + in-tree status + custom-type layer**. It does
not re-catalogue what existing research already covers — see
[`chacha_poly_tag_bug_2026-04-17.md`](chacha_poly_tag_bug_2026-04-17.md) and the
`doc/01_research/lib/serialization/data_format_parser_security_2026-01-31.md`
parser-hardening research for adjacent material.

## Purpose & the actual target

The dominant target of this wave is **improving the Simple language itself**.
Crypto/search/compression are the *vehicle*: they are byte-heavy, type-heavy,
generics-heavy, and they already have partial in-tree implementations built on
**primitives** (`[u8]`, `i64`, `text`). Rebuilding them on **intensive custom
types** (spans, views, fixed-width integers, bit cursors, tagged digests, keys,
nonces) deliberately stresses the type system, generics (`<>`), traits/mixins,
`me`-self-mutation, and operator forms — and every place that forces a primitive
workaround becomes a concrete language bug/feature item (see the plan's capture
loop).

## In-tree status (what is already implemented)

| Area | In-tree | Path | Notes |
|------|---------|------|-------|
| SHA-256 / SHA-512 | yes | `src/lib/common/crypto/sha256.spl`, `sha512.spl` | primitive (`[u8]`) based |
| HMAC / HKDF | yes | `src/lib/common/crypto/hmac.spl`, `hkdf.spl` | |
| ECDSA P-256 | yes | `src/lib/common/crypto/ecdsa_p256.spl` | |
| constant-time helpers | yes | `src/lib/common/crypto/constant_time.spl` | reuse for all comparisons |
| AES | yes | `src/lib/common/aes/` | |
| RSA (modexp) | yes | `src/lib/common/rsa/`; plan `rsa_modexp_montgomery_barrett.md` | |
| bcrypt / scrypt | yes | `src/lib/common/bcrypt/`, `scrypt/` | |
| secure random | yes | `src/lib/common/secure_random/` | |
| signatures | yes | `src/lib/common/signature/` | |
| JWT | yes | `src/lib/common/jwt/` | |
| AES-128-GCM / AES-256-GCM | yes | `src/os/crypto/aes128_gcm.spl`, `aes256_gcm.spl` | recent baremetal-safety fixes |
| Ed25519 / X25519 / SHA-KDF | yes (rv64 live) | `src/os/crypto/`, `src/os/apps/sshd/ssh_kex_crypto.spl` | alpha pure-vs-C lane |
| **dual-backend engine** | yes | `src/os/crypto/dual_backend.spl` | alpha/beta/normal; **primitive-typed seam** |
| ChaCha20-Poly1305 | partial/bug | research `chacha_poly_tag_bug_2026-04-17.md` | tag mismatch tracked |

**Conclusion:** crypto is the most-mature domain and already owns the alpha
dual-backend engine. That is exactly why the companion plan uses crypto as the
**template** and hosts the authoritative shared custom-type foundation.

## Alpha mode recap (existing contract)

`src/os/crypto/dual_backend.spl` defines `DualBackendMode`:
- **alpha** (default): run runtime-backed (C) *and* pure-Simple, compare, **stop
  on mismatch** (fail-closed). This is the parity oracle.
- **beta**: run both, log a reproducible diff report, return preferred backend.
- **normal**: single implementation on the hot path; other side only on empty.

Today the seam is primitive: `dual_backend_run_bytes/_bool/_u64/_text`. The
custom-type seam decision (convert at boundary vs. generic-over-custom-type) is
itself a language probe — see plan §"dual_backend seam".

## Custom-type layer (the new design axis)

Primitives extracted → custom types. Authoritative spec lives in the crypto plan
§Phase-0 (shared foundation, `src/lib/common/bytes/`). Crypto-specific types:

| Primitive today | Custom type | Behavior it must carry |
|-----------------|-------------|------------------------|
| `[u8]` key material | `SecretKey`, `PublicKey` | zeroize-on-drop intent, length invariant, no `Display` of secret bytes |
| `[u8]` nonce/iv | `Nonce<N>` | fixed width, single-use marker, increment op |
| `[u8]` digest | `Digest<N>` | constant-time `==` only, hex via explicit method |
| `[u8]` tag | `AuthTag` | constant-time verify, never `==` on raw bytes |
| `[u8]` plaintext/ciphertext | `Plaintext` / `Ciphertext` (newtype over `ByteSpan`) | prevents mixing AAD/PT/CT at call sites |
| `i64` field element | `FieldElem` / `Scalar` | modular `+ - *`, reduction, from/to bytes |
| `text` algorithm id | `AlgId` enum | versioned negotiation, no stringly-typed dispatch |

Design rule (from advisor): **types must carry behavior** (methods, trait
conformance, generics, `me`-self-mutation, operators). Inert newtypes won't
stress the compiler and won't surface language items.

## Catalog (external map; scope decisions live in the plan)

Primitive / mode / scheme / protocol / format / library distinction follows the
source brief. Compressed here to the engineering-relevant rows; the plan picks a
deliberately narrow staged subset.

- **Symmetric**: AES (128/192/256), ChaCha20/XChaCha20, Salsa20; legacy/regional
  (3DES, Camellia, ARIA, SEED, SM4, GOST/Kuznyechik); lightweight (Ascon, GIFT,
  PRESENT, SPECK, LEA, HIGHT).
- **AEAD/modes**: AES-GCM (+SIV), AES-CCM, ChaCha20-Poly1305, XChaCha20-Poly1305,
  AES-OCB, Ascon-AEAD; block modes CTR/CBC/XTS/KW/SIV.
- **Hash/XOF/MAC**: SHA-2, SHA-3/SHAKE, BLAKE2/BLAKE3, SM3, Streebog; HMAC, KMAC,
  CMAC, GMAC, Poly1305, SipHash.
- **KDF/PW/DRBG**: HKDF, PBKDF2, SP800-108; Argon2id, scrypt, bcrypt, yescrypt;
  CTR_DRBG, HMAC_DRBG, Hash_DRBG, ChaCha20-RNG.
- **Public-key/KEM/sig**: X25519/X448, ECDH P-256/384/521, RSA-OAEP/PSS, Ed25519/
  Ed448, ECDSA; PQ: ML-KEM, ML-DSA, SLH-DSA, Falcon, LMS/XMSS; HPKE.
- **Advanced**: Shamir/Feldman/Pedersen secret sharing, FROST/threshold sigs,
  PAKE (OPAQUE/SPAKE2/CPace/SRP), OPRF, VRF, VDF, commitments (Pedersen/KZG),
  ZK (Schnorr/Bulletproofs/Groth16/PLONK/STARK), MPC, HE (Paillier/BFV/CKKS/TFHE),
  OT, group/blind signatures.
- **Protocols**: TLS 1.3/1.2, DTLS, QUIC, SSH-2, IPsec/IKEv2, WireGuard/Noise,
  WPA2/3, Kerberos, DNSSEC, MLS, Signal (X3DH+Double Ratchet); message/object:
  OpenPGP, CMS/PKCS#7, JOSE (JWS/JWE/JWT/JWK), COSE/CWT, age, minisign, ACME, CT,
  OCSP/CRL; identity: OAuth2, OIDC, SAML, WebAuthn/FIDO2, SCRAM.
- **Formats**: PEM/DER/BER, X.509, PKCS#1/8/10/12, SPKI, JWK/JWS/JWE/JWT,
  COSE_Key, OpenPGP packets, SSH key formats, WireGuard config, TPM2B.

### Legacy / avoid (do **not** add new pure-Simple impls)
MD5, SHA-1 signatures, DES/3DES, RC4, ECB, unauthenticated CBC, RSA PKCS#1 v1.5
encryption, DSA, static-RSA TLS, SSLv2/3/TLS1.0/1.1, WEP/TKIP, PPTP/MS-CHAPv2,
A5/1, Rainbow/SIKE (broken PQ). Keep only for decode/compat behind explicit gates.

## C reuse license gate (permissive ⇒ may vendor/bind; else write own C)

| Library | License | Reuse posture |
|---------|---------|---------------|
| libsodium | ISC | **permissive** — preferred C oracle for AEAD/sig/KX |
| BearSSL | MIT-like | **permissive** — small TLS/primitives oracle |
| Monocypher | BSD/CC0 | **permissive** — embedded oracle |
| OpenSSL 3.x | Apache-2.0 | **permissive** — broad oracle |
| mbed TLS | Apache-2.0 OR GPL | permissive via Apache option |
| liboqs / PQClean | MIT | **permissive** — PQ oracle |
| HACL*/EverCrypt | Apache/MIT | **permissive** — verified oracle |
| wolfSSL | GPL-3.0 (or commercial) | **copyleft ⇒ write own C** for the parity oracle |
| GnuTLS / libgcrypt | LGPL/GPL | copyleft ⇒ prefer permissive alt or own C |

Vendored C must land under owned-code-scope external paths
(`src/runtime/vendor/**`), never mixed into owned `.spl`/`.c`.

## Verification implications
- Alpha parity (C oracle vs pure-Simple) byte-for-byte, including AEAD tag verify
  via constant-time `AuthTag`, not `==`.
- NIST/RFC test vectors as typed fixtures (`Digest<N>` / `Nonce<N>` literals),
  not loose hex strings.
- `bin/simple test`, `bin/simple build lint`, and the rv64 live lane for the SSH
  cipher set remain the gates (see existing `os/crypto` specs).
