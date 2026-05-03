# Crypto Algorithms — Agent Task Plan (2026-05-03)

## Status Summary

| Category | Implemented | Needs Fix/Spec | Not Started |
|----------|-------------|----------------|-------------|
| Block Ciphers | 14 | 2 | 0 |
| Stream Ciphers | 5 | 0 | 0 |
| AEAD | 8 | 0 | 0 |
| Hashes | 16 | 0 | 0 |
| KDF/Password | 9 | 0 | 0 |
| MAC | 8 | 1 | 0 |
| Asymmetric/Sigs | 10 | 2 | 1 |
| Key Exchange | 5 | 1 | 0 |
| PQC | 7 | 1 | 0 |

---

## Block Ciphers (`src/os/crypto/`)

### Done (14)
| Module | Standard | Tests |
|--------|----------|-------|
| `aes_modes.spl` | AES-128/256 ECB/CBC | pass |
| `aes128_gcm.spl` | AES-128-GCM | pass |
| `aes256_gcm.spl` | AES-256-GCM | pass |
| `aes_gcm_siv.spl` | AES-GCM-SIV RFC 8452 | pass |
| `aes_modes.spl` | AES-OFB/CFB | pass |
| `camellia.spl` | Camellia RFC 3713 | pass (8 KAT) |
| `aria.spl` | ARIA RFC 5794 | pass (8 KAT) |
| `seed.spl` | SEED RFC 4269 | pass (12 KAT) |
| `tea.spl` | TEA + XTEA | pass (12) |
| `twofish.spl` | Twofish | pass (8 KAT) |
| `sm4.spl` | SM4 GB/T 32907 | pass (8) — fixed W37-B |
| `serpent.spl` | Serpent AES finalist | in progress (W37-H) |
| `rc4.spl` | RC4 (legacy) | pass |
| `aes_xts.spl` | AES-XTS IEEE 1619 | impl done, spec blocked (#115) |

### Needs Fix/Spec (2)
| Module | Issue | Agent |
|--------|-------|-------|
| `aes256_ccm.spl` | AES-256-CCM stalled, needs spec | unassigned |
| `aes_xts.spl` | Blocked by `expect_byte_array` bug (#115) | unassigned |

---

## Stream Ciphers

### Done (5)
| Module | Standard | Tests |
|--------|----------|-------|
| `chacha20.spl` | ChaCha20 RFC 8439 | pass |
| `salsa20.spl` | Salsa20/20 | pass (KAT) |
| `xsalsa20.spl` | XSalsa20 (HSalsa20+Salsa20) | pass |
| `zuc.spl` | ZUC 128-EEA3 | pass |
| `snow3g.spl` | SNOW 3G | pass |

---

## AEAD Modes

### Done (8)
| Module | Standard | Tests |
|--------|----------|-------|
| `aes128_gcm.spl` | AES-128-GCM | pass |
| `aes256_gcm.spl` | AES-256-GCM | pass |
| `aes_gcm_siv.spl` | AES-GCM-SIV RFC 8452 | pass |
| `chacha20_poly1305.spl` | ChaCha20-Poly1305 RFC 8439 | pass |
| `aes_cmac.spl` | AES-CMAC RFC 4493 | pass |
| EAX (in `aes_modes`) | EAX mode | pass |
| `ocb3.spl` | OCB3 AEAD | pass (focused encrypt/decrypt conformance) |

---

## Hashes (`src/os/crypto/` + `src/lib/common/hash/`)

### Done (16)
| Module | Standard | Tests |
|--------|----------|-------|
| `sha256.spl` | SHA-256 + HMAC-SHA-256 | pass |
| `sha224.spl` | SHA-224 | pass |
| `sha384.spl` | SHA-384 | pass (fixed W16-B) |
| `sha512.spl` | SHA-512 | pass |
| SHA-3 family | SHA3-256/384/512 + SHAKE | pass |
| `blake2b.spl` | BLAKE2b | pass |
| `blake2s.spl` | BLAKE2s | pass |
| `blake3.spl` | BLAKE3 | pass (extended KAT) |
| `ripemd160.spl` | RIPEMD-160 | pass |
| `tiger.spl` | Tiger | pass (5 KAT) |
| `whirlpool.spl` | Whirlpool ISO 10118-3 | pass (3 KAT) — fixed W37-I |
| `sm3.spl` | SM3 GB/T 32905 | pass (3 KAT) — fixed W37 |
| `streebog.spl` | Streebog / GOST R 34.11-2012 | pass (focused RFC KAT) |
| `siphash.spl` | SipHash-2-4 + SipHash-1-3 | pass |
| `adler32.spl` | Adler-32 + Fletcher-32 | pass (11) |
| `crc32.spl` | CRC-32 + CRC-32C | pass |

---

## KDF / Password Hashing

### Done (9)
| Module | Standard | Tests |
|--------|----------|-------|
| `pbkdf2.spl` | PBKDF2-SHA-256 RFC 8018 | pass (3) |
| PBKDF1 | RFC 2898 §5.1 | pass |
| HKDF | RFC 5869 (SHA-256, SHA-512) | pass |
| HMAC-DRBG | NIST SP 800-90A | pass |
| `bcrypt.spl` | bcrypt | pass |
| `scrypt.spl` | scrypt RFC 7914 | pass |
| `argon2.spl` | Argon2id RFC 9106 | pass |
| `argon2d.spl` | Argon2d + Argon2i | pass |
| HOTP/TOTP | RFC 4226/6238 | pass |

---

## MAC

### Done (8)
| Module | Standard |
|--------|----------|
| HMAC-SHA-256 | RFC 2104 |
| HMAC-SHA-384/512 | RFC 2104 |
| HMAC-SHA3 | NIST |
| HMAC-RIPEMD-160 | |
| HMAC-BLAKE2b/2s | keyed |
| AES-CMAC | RFC 4493 |
| GMAC | standalone |
| Poly1305 | RFC 8439 |

### Needs Spec (1)
| Module | Issue |
|--------|-------|
| `kmac.spl` + `cshake.spl` | Files exist, KAT spec never converged |

---

## Asymmetric / Signatures

### Done (10)
| Module | Standard | Tests |
|--------|----------|-------|
| `ed25519.spl` | Ed25519 RFC 8032 | pass |
| `ed448.spl` | Ed448 RFC 8032 §5.2 | pass |
| `rsa_pss.spl` | RSA-PSS RFC 8017 | pass |
| `ecdsa_p256.spl` | P-256 ECDSA (FFI wrapper) | pass |
| `p256.spl` | P-256 pure-Simple | fixing (W37-A) |
| `ml_dsa.spl` | ML-DSA-65 FIPS 204 | pass |
| ML-DSA-44/87 | FIPS 204 variants | pass |
| `slh_dsa.spl` | SLH-DSA-128s FIPS 205 | pass |
| X.509 v3 parser | RFC 5280 | pass |
| `curve25519.spl` | Curve25519 field arith | pass |

### In Progress (2)
| Module | Agent |
|--------|-------|
| `p256.spl` fix (1 test failing) | W37-A running |
| `p384.spl` new pure-Simple | W37-L running |

### Not Started (1)
| Module | Blocker |
|--------|---------|
| SLH-DSA-192s/256s | Hash-fn parameterization (#109) |

---

## Key Exchange

### Done (5)
| Module | Standard |
|--------|----------|
| X25519 | RFC 7748 |
| X448 | RFC 7748 |
| ECDH-P256 | via ecdsa_p256.spl |
| `ffdhe.spl` | RFC 7919 (file exists) |
| `curve448.spl` | Curve448 field arith |

### In Progress (1)
| Module | Agent |
|--------|-------|
| P-384 ECDH | W37-L running |

---

## PQC (Post-Quantum)

### Done (7)
| Module | Standard |
|--------|----------|
| ML-KEM-768 | FIPS 203 |
| ML-KEM-512 | FIPS 203 |
| ML-KEM-1024 | FIPS 203 |
| ML-DSA-65 | FIPS 204 |
| ML-DSA-44 | FIPS 204 |
| ML-DSA-87 | FIPS 204 |
| SLH-DSA-128s | FIPS 205 |

### Blocked (1)
| Module | Blocker |
|--------|---------|
| SLH-DSA-192s/256s | Hash-fn parameterization |

---

## Agent Spawn Guide

Each agent receives:
- **File scope**: single `.spl` file + its test spec (disjoint from other agents)
- **Workarounds**: avoid `pass`/`out`/`val` param names, use `var` before push, use `elif` not sequential `if-return`
- **Commit**: `jj commit -m "feat(crypto): ..."` — run `rm -f .git/index.lock` first
- **Verify**: `bin/simple test test/unit/os/crypto/<spec>.spl` must pass
- **advisor()**: call before substantive work and before declaring done
