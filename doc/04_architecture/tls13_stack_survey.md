# TLS 1.3 Stack Survey and Gap Analysis

**Date:** 2026-05-01
**Scope:** `src/os/tls13/` — client-only TLS 1.3 implementation  
**RFC reference:** RFC 8446 (TLS 1.3)  
**Status:** Survey + gap analysis against RFC 8446 required components.

---

## 1. Goal

This document maps what is actually present in `src/os/tls13/` against the
components mandated by RFC 8446, so future work has a concrete checklist of
what is done, what is partial, and what is absent.  The TLS 1.3 stack
underpins HTTPS for SimpleOS's browser and hosted networking layers.  The
survey is ground-truth only; every claim was verified against source files.

---

## 2. RFC 8446 Component Checklist

| Component | RFC 8446 § | In tree? | Module / Notes |
|---|---|---|---|
| Record layer (TLSPlaintext / TLSCiphertext framing) | §5 | ✓ | `record13.spl` |
| Record-layer AEAD encrypt/decrypt | §5.2 | ✓ | `record13.spl` — AES-128-GCM only |
| Handshake protocol state machine | §4 | ✓ client-only | `tls13.spl` |
| Key schedule (HKDF-Extract / Expand-Label) | §7.1 | ✓ | `hkdf.spl`, `key_schedule.spl` |
| ClientHello | §4.1.2 | ✓ | `handshake13.spl` |
| ServerHello | §4.1.3 | ✓ parse | `handshake13.spl` |
| HelloRetryRequest | §4.1.4 | ✗ | Not handled — server HRR causes failure |
| EncryptedExtensions | §4.3.1 | ⚠ partial | `handshake13.spl` — parsed but not validated |
| CertificateRequest | §4.3.2 | ✓ | `handshake13.spl` — client auth flow present |
| Certificate | §4.4.2 | ✓ | `handshake13.spl`, `cert_verify.spl` |
| CertificateVerify | §4.4.3 | ✓ Ed25519 + RSA-PSS | `cert_verify.spl` — ECDSA dispatch absent |
| Finished | §4.4.4 | ✓ | `handshake13.spl`, `key_schedule.spl` |
| KeyUpdate | §4.6.3 | ✗ | No post-handshake message handling |
| NewSessionTicket | §4.6.1 | ✗ | Received tickets are silently ignored |
| Alert protocol | §6 | ⚠ partial | `close_notify` sent; inbound alerts not parsed |
| Extensions: supported_versions | §4.2.1 | ✓ | `handshake13.spl` |
| Extensions: key_share (X25519) | §4.2.8 | ✓ X25519 only | `handshake13.spl` |
| Extensions: SNI | §4.2.11 | ✓ | `handshake13.spl` |
| Extensions: signature_algorithms | §4.2.3 | ⚠ narrow | advertises Ed25519 only; verifies Ed25519 + RSA-PSS |
| Extensions: supported_groups | §4.2.7 | ⚠ narrow | X25519 only |
| Extensions: ALPN | §4.2.11 | ✗ | No ALPN builder or parser in TLS layer |
| 0-RTT / early_data | §4.2.10 | ✗ | Not implemented |
| PSK / pre_shared_key | §4.2.11 | ✗ | Not implemented |
| Cipher suite: TLS_AES_128_GCM_SHA256 | §B.4 | ✓ | Only suite advertised (0x1301) |
| Cipher suite: TLS_AES_256_GCM_SHA384 | §B.4 | ✗ wire | AES-256-GCM is in `os/crypto/` but not wired in TLS |
| Cipher suite: TLS_CHACHA20_POLY1305_SHA256 | §B.4 | ✗ wire | ChaCha20-Poly1305 is in `os/crypto/` but not wired in TLS |
| Transcript hash (SHA-256) | §7.1 | ✓ | `transcript.spl` — SHA-256 only |
| Transcript hash (SHA-384, for AES-256 suite) | §7.1 | ✗ | transcript.spl is SHA-256-only |
| Downgrade protection (§4.1.3 random sentinel) | §4.1.3 | ✗ | Not checked in parse_server_hello |
| Server-side TLS 1.3 (accept / ServerHello send) | — | ✗ | Stack is client-only |

---

## 3. What is in `src/os/tls13/`

### 3.1 `mod.spl` — 11 lines

Module root; re-exports the public surface of the TLS 1.3 package.  Contains
only `use` declarations.  No logic.

### 3.2 `tls13.spl` — 1,247 lines

**Main orchestrator — client-only state machine.**

Implements `tls13_connect`, `tls13_connect_host_stream`,
`tls13_connect_io_with_config`, `tls13_send`, `tls13_recv`, and
`tls13_close`.  The connect path follows RFC 8446's client flow in 14
numbered steps:

1. Generate X25519 ephemeral keypair.
2. Build and send ClientHello plaintext record; add to transcript.
3. Read and parse ServerHello; add to transcript.
4. Compute X25519 shared secret and handshake secrets.
5–13. Read encrypted handshake records, dispatch on message type:
  EncryptedExtensions, CertificateRequest (optional), Certificate,
  CertificateVerify, server Finished.
14. Verify server CertificateVerify and Finished; derive app secrets;
    optionally send client Certificate + CertificateVerify; send client
    Finished.

Two I/O modes are supported: a native TCP fd path (baremetal/SimpleeOS)
and a `host_stream` path (hosted/Linux).  The fd path uses `rt_*` extern
fast-paths for several crypto operations (HKDF, SHA-256, AES-GCM); the
host_stream path uses pure-Simple implementations in the other modules.

The `Tls13Context` returned after handshake carries separate `server_key` /
`client_key` (`RecordKey`) and sequence numbers for application data.

**Gaps noted in source:**
- Inbound `alert` records (content_type 0x15) are skipped rather than
  dispatched; only `close_notify` is sent outbound.
- No `KeyUpdate` or `NewSessionTicket` handler.
- `HelloRetryRequest` is not distinguished from `ServerHello`; a server
  sending HRR will be mishandled.
- Downgrade sentinel check on `ServerHello.random` bytes 24–31 is absent.
- Static client random (hardcoded test vector) used in some paths — must be
  replaced with `random_bytes(32)` for production.

### 3.3 `handshake13.spl` — 627 lines

**Wire-format encoder/decoder — pure Simple, no crypto.**

Defines all handshake message type constants (`HS_CLIENT_HELLO`,
`HS_SERVER_HELLO`, etc.) and extension type constants (`EXT_SNI`,
`EXT_KEY_SHARE`, `EXT_SUPPORTED_VERSIONS`, `EXT_SIG_ALGS`,
`EXT_SUPPORTED_GROUPS`).

Public functions:

- `build_client_hello_bytes` — encodes a minimal ClientHello with five
  extensions: supported_versions, key_share (X25519), SNI, sig_algs
  (Ed25519 only), supported_groups (X25519 only).
- `parse_server_hello` — decodes ServerHello; extracts random, cipher
  suite, and X25519 public key from key_share.
- `parse_handshake_header` — reads the 4-byte TLS handshake header.
- `parse_encrypted_extensions` — returns `bool`; extension bytes are read
  but semantics are not validated (ALPN, etc. are ignored).
- `parse_certificate_body`, `parse_certificate_chain_body` — DER cert
  extraction from Certificate message.
- `parse_certificate_request` — extracts request_context and sig_algs.
- `parse_certificate_verify` — returns `CertVerifyFields` (algorithm, sig).
- `parse_finished_body` — extracts verify_data.
- `build_finished_bytes`, `build_certificate_bytes`,
  `build_certificate_verify_bytes` — encode client-side messages.

**Gaps:**
- Only `TLS_AES_128_GCM_SHA256` (0x1301) is advertised; no multi-suite
  negotiation logic.
- No ALPN extension builder.
- `parse_encrypted_extensions` does not surface ALPN or other extensions to
  the caller.
- No HelloRetryRequest distinguished from ServerHello.

### 3.4 `record13.spl` — 365 lines

**TLS 1.3 AEAD record layer — pure Simple, baremetal-safe.**

Implements RFC 8446 §5.2 TLSInnerPlaintext / TLSCiphertext framing.

Functions:
- `record13_make_nonce` — XOR of per-record-key IV and 8-byte big-endian
  sequence number.
- `record13_build_header` — 5-byte TLSCiphertext header (type 0x17,
  legacy version 0x0303, length).
- `record13_encrypt(key, seq, content_type, plaintext)` — appends
  content_type byte, encrypts with AES-128-GCM via `aes128_gcm_encrypt`,
  prepends the 5-byte header.
- `record13_decrypt(key, seq, raw_record)` — validates header, strips AEAD
  tag, decrypts, strips inner content_type byte.
- `record13_decrypt_fd_inner` — variant used on the fd fast path.

The `RecordKey` type holds a 16-byte AES-128 key and 12-byte IV.

**Gaps:**
- Hardwired to AES-128-GCM.  Supporting AES-256-GCM or ChaCha20-Poly1305
  requires a `RecordKey` cipher-suite tag and dispatch in encrypt/decrypt.
- No record size limit enforcement beyond the AEAD tag minimum; RFC 8446
  §5.2 mandates rejection of records exceeding 2^14 + 256 bytes.

### 3.5 `key_schedule.spl` — 179 lines

**TLS 1.3 key schedule — RFC 8446 §7.1.**

Implements the full three-step secret ladder:
`early_secret → handshake_secret → master_secret`, plus:

- `derive_secret(secret, label, transcript)` — HKDF-Expand-Label with
  transcript hash as context.
- `tls13_early_secret` — `HKDF-Extract(0…0, 0…0)`.
- `tls13_compute_handshake_secrets` — derives
  `client_hs_traffic` / `server_hs_traffic` from ECDHE shared secret.
- `tls13_compute_app_secrets` — derives `client_app_traffic` /
  `server_app_traffic`.
- `tls13_traffic_keys` — `HKDF-Expand-Label("key")` + `("iv")` → 16-byte
  AES-128 key + 12-byte IV.
- `tls13_finished_key`, `tls13_verify_data` — `HMAC-SHA-256`-based
  Finished MAC.

**Gaps:**
- Traffic key derivation is hardcoded for AES-128 (16-byte key).  SHA-384
  and 32-byte keys needed for `TLS_AES_256_GCM_SHA384`.
- No resumption / PSK branch in the early-secret step.

### 3.6 `hkdf.spl` — 301 lines

**HKDF (RFC 5869) with SHA-256.**

Implements `hkdf_extract`, `hkdf_expand`, and `hkdf_expand_label`
(RFC 8446 §7.1 HkdfLabel encoding).  Each function has a runtime fast-path
via `rt_tls13_hkdf_extract_into` / `rt_tls13_hkdf_expand_label_*` externs
and falls back to pure-Simple `sha256_hmac`.

> **Note:** A feature-request doc (`doc/08_tracking/feature_request/hkdf_rfc5869_2026-05-01.md`)
> proposes a canonical `src/lib/common/crypto/hkdf.spl`.  That is a stdlib
> promotion task.  The TLS-local `os/tls13/hkdf.spl` is already present and
> functional.

**Gaps:**
- SHA-256 only.  SHA-384 HKDF (needed for `TLS_AES_256_GCM_SHA384`) is not
  implemented.
- No test vectors in-module; verification relies on the TLS integration path.

### 3.7 `transcript.spl` — 55 lines

**Running SHA-256 transcript hash — immutable accumulator.**

`Transcript` is a struct holding a byte buffer and length.
`transcript_add` / `transcript_add_with_len` return a new `Transcript`.
`transcript_hash` calls `rt_tls13_sha256` (runtime fast path) or
`sha256_with_len` (pure Simple).

**Gaps:**
- SHA-256 only — no SHA-384 path, which blocks `TLS_AES_256_GCM_SHA384`.
- `transcript_add_with_len` only works when the full message is already
  buffered; streaming accumulation is not supported.

### 3.8 `cert_verify.spl` — 711 lines

**X.509 DER parsing and certificate signature verification.**

Implements:
- DER TLV helpers: `_der_read_tlv`, `_der_skip`, tag/length/value parsing.
- `extract_ed25519_pubkey_from_cert` — navigates DER to SubjectPublicKeyInfo,
  checks OID `1.3.101.112`, returns raw 32-byte Ed25519 key.
- `extract_rsa_pubkey_spki_from_cert` — returns raw SPKI TLV bytes for RSA
  keys.
- `verify_certificate_verify_msg_scheme(pubkey, sig_scheme, transcript_hash, sig)` —
  builds the RFC 8446 §4.4.3 signed content (64×0x20 || context string ||
  0x00 || hash) and dispatches on `sig_scheme`:
  - `0x0807` ed25519 — calls `ed25519_verify` from `os.crypto.ed25519`.
  - `0x0804` rsa_pss_rsae_sha256 — calls `rsa_pss_sha256_verify`.
  - `0x0805` rsa_pss_rsae_sha384 — calls `rsa_pss_sha384_verify`.
  - `0x0806` rsa_pss_rsae_sha512 — calls `rsa_pss_sha512_verify`.
- `verify_cert_chain(chain, root_store)` — leaf-first chain walk; checks
  issuer/subject name match, CA flag, and signature for each link.
- `verify_cert_signature_ed25519` — verifies a certificate's self/issuer
  signature (Ed25519 only at this point).

**Gaps:**
- **No ECDSA signature-scheme dispatch** — `ecdsa_secp256r1_sha256` (0x0403),
  `ecdsa_secp384r1_sha384` (0x0503), and `ecdsa_secp521r1_sha512` (0x0603)
  return `Err("unsupported signature scheme")`.  Servers presenting
  ECDSA-signed certificates will fail.
- `verify_cert_chain` does not enforce validity period (NotBefore /
  NotAfter) — expired certificates are accepted.
- No hostname / SAN matching — `Tls13ClientConfig.root_store` is used for
  chain trust but no leaf CN/SAN is checked against SNI.
- `verify_cert_chain` skips signature verification when `root_store` is
  empty (falls through without error for the last link), making pinless
  validation unsafe.

### 3.9 `test_server_config.spl` — 122 lines

**Test fixture: TLS server SDN configuration.**

Provides `tls_test_server_default_config` and `load_tls_test_server_config`
for use by integration tests.  Not part of the production TLS API.

---

## 4. Crypto Primitive Backing Matrix

| TLS 1.3 needs | Status | Source | Note |
|---|---|---|---|
| AES-128-GCM (encrypt + decrypt) | ✓ in tree | `os/crypto/aes128_gcm.spl` (620 lines) | Pure Simple + runtime helpers `rt_aes_sbox/rcon/rt_aes128_encrypt_block_into`; fast path via `rt_tls13_aes128_gcm_encrypt`. Used by `TLS_AES_128_GCM_SHA256`. |
| AES-256-GCM | ✓ in tree, not wired | `os/crypto/aes_gcm.spl` | `aes256_gcm_encrypt/decrypt` exist but TLS record layer does not call them; `TLS_AES_256_GCM_SHA384` not advertised. |
| ChaCha20-Poly1305 | ✓ in tree, not wired | `os/crypto/chacha20_poly1305.spl` | Functions exist; not wired into `record13.spl` or `handshake13.spl`. |
| SHA-256 | ✓ | `os/crypto/sha256.spl` | Used by transcript, HKDF, HMAC-Finished. Runtime fast path via `rt_tls13_sha256`. |
| SHA-384 | ✓ in tree (via SHA-512) | `os/crypto/sha512.spl` | SHA-512 is present; SHA-384 is a truncation — not yet exposed as a named function. Not wired into TLS. |
| HMAC-SHA-256 | ✓ | `os/crypto/sha256.spl` (`sha256_hmac`) | Used by HKDF and Finished. |
| HMAC-SHA-384 | ✗ | — | Needed for HKDF-SHA-384 (AES-256 suite); not present. |
| HKDF-Extract (SHA-256) | ✓ | `os/tls13/hkdf.spl` | Full RFC 5869 implementation with runtime fast path. |
| HKDF-Expand (SHA-256) | ✓ | `os/tls13/hkdf.spl` | Full iterative HMAC chain. |
| HKDF-Expand-Label (RFC 8446 §7.1) | ✓ | `os/tls13/hkdf.spl` | HkdfLabel encoding present. |
| HKDF-SHA-384 path | ✗ | — | Needed for `TLS_AES_256_GCM_SHA384`; absent. |
| X25519 (ECDHE key exchange) | ✓ | `os/crypto/curve25519.spl` | Pure Simple bigint implementation; RFC 7748. |
| Ed25519 verify | ✓ | `os/crypto/ed25519.spl` | Pure Simple; runtime fast path via `rt_ed25519_verify`. No known wrapper bug in the verify path. |
| Ed25519 sign (client auth) | ✓ | `os/crypto/ed25519.spl` | `rt_ed25519_sign` extern; used by client CertificateVerify. |
| ECDSA-P256 (signature verify) | ✓ in crypto, ✗ in TLS | `os/crypto/ecdsa_p256.spl` | P256 implementation exists but cert_verify dispatcher does not handle 0x0403/0x0503/0x0603. |
| RSA-PSS-SHA-256/384/512 verify | ✓ (FFI) | `std.nogc_sync_mut.io.signature_ffi` | `rsa_pss_sha*_verify` externs; wired in cert_verify dispatcher. |
| ML-KEM-768 (post-quantum) | ✗ | — | Not in tree; see `pqc_hybrid_kex_design.md`. |

---

## 5. Wire-Format Gaps

The following RFC 8446 wire-format elements are missing or incomplete in
the current tree:

### 5.1 Record layer

- **Single cipher suite hardwired.** `record13.spl` always uses AES-128-GCM.
  The `RecordKey` struct has no cipher-suite tag; adding AES-256-GCM or
  ChaCha20-Poly1305 requires a structural change.
- **No record size limit.** RFC 8446 §5.2 says reject records with
  `length > 2^14 + 256`.  No such check exists in `record13_decrypt`.

### 5.2 Handshake protocol

- **HelloRetryRequest (HRR).** A server responding with HRR (distinguished
  by `ServerHello.random == HelloRetryRequest_sentinel`) is not detected;
  the state machine will attempt to process it as a normal ServerHello and
  fail with a key-schedule error.
- **Downgrade detection.** RFC 8446 §4.1.3 requires the client to abort if
  `ServerHello.random[24..32]` equals the TLS 1.2 or TLS 1.3 downgrade
  sentinels.  Not checked.
- **EncryptedExtensions not semantically parsed.** The parser returns `bool`
  and discards ALPN, max_fragment_length, and all other extensions.
- **No ALPN.** The ClientHello has no ALPN extension builder.  Servers that
  require protocol negotiation (e.g., HTTP/2) will reject the handshake.
- **Signature algorithms narrow.** ClientHello advertises Ed25519 only.
  Most real-world servers use ECDSA-P256 or RSA-PSS; they may reject a
  ClientHello that does not list their preferred scheme, or the
  CertificateVerify dispatch will fail for 0x0403.

### 5.3 Certificate validation

- **No ECDSA CertificateVerify dispatch.** The largest gap for
  browser-level HTTPS: practically all public CAs sign with ECDSA-P256
  (0x0403) or RSA-PSS.  The verifier handles RSA-PSS but returns an error
  for all ECDSA schemes.
- **No hostname / SAN matching.** A valid chain with a mismatched hostname
  is accepted.
- **No validity-period check.** `cert_verify.spl` reads but ignores
  NotBefore / NotAfter fields.
- **Pinless root store is unsafe.** When `root_store` is empty the chain
  walk exits without verifying the final link's signature.

### 5.4 Post-handshake messages

- **KeyUpdate** — not handled; receipt is ignored.
- **NewSessionTicket** — received tickets are silently ignored; resumption
  via PSK is not possible.
- **0-RTT / early_data** — not implemented.

### 5.5 Server-side TLS

The stack is client-only.  There is no `tls13_accept` or server-side
handshake state machine.

---

## 6. Recommended Priority Order for Landing TLS 1.3

The following ordering targets a minimal but secure HTTPS client usable
against real-world servers (e.g., connecting to api.github.com).

### Priority 1 — Foundation (unblock real servers)

1. **ECDSA-P256 CertificateVerify dispatch in `cert_verify.spl`.**
   Add `0x0403` / `0x0503` / `0x0603` branches calling
   `ecdsa_p256_verify` from `os/crypto/ecdsa_p256.spl`.  This is the
   single biggest blocker: most public TLS servers present ECDSA certs.

2. **ECDSA in ClientHello `signature_algorithms`.** Extend
   `_build_ext_sig_algs` in `handshake13.spl` to advertise
   `ecdsa_secp256r1_sha256` (0x0403) alongside Ed25519.  Without this,
   servers may abort the handshake before sending their cert.

3. **Hostname / SAN matching in `cert_verify.spl`.** Parse leaf CN and
   Subject Alternative Name extension; compare against SNI hostname.

4. **HelloRetryRequest detection.** Check
   `ServerHello.random == HRR_SENTINEL` and return a clear error rather
   than mishandling it.  Add HRR retry logic if a second group advertisement
   is needed.

5. **Downgrade sentinel check.** Add RFC 8446 §4.1.3 random-bytes check
   after parsing ServerHello.

### Priority 2 — Record layer breadth (two more cipher suites)

6. **ALPN extension.** Add `_build_ext_alpn(protocols: [text])` in
   `handshake13.spl`; parse it from EncryptedExtensions.  Required for
   HTTP/2 (h2) negotiation.

7. **AES-256-GCM-SHA384 cipher suite.** Add SHA-384 transcript hash
   (truncate SHA-512 from `sha512.spl`), SHA-384 HKDF path in `hkdf.spl`,
   32-byte key derivation in `key_schedule.spl`, and AES-256-GCM dispatch
   in `record13.spl` / `record13_encrypt` / `record13_decrypt`.

8. **ChaCha20-Poly1305-SHA256 cipher suite.** Wire `chacha20_poly1305.spl`
   into the record layer.  The primitive is already implemented.

### Priority 3 — Robustness

9. **Record size enforcement.** Reject `length > 2^14 + 256` in
   `record13_decrypt`.

10. **Certificate validity period.** Check NotBefore / NotAfter in
    `verify_cert_chain`.

11. **Root-store empty guard.** Return an error when `root_store` is empty
    rather than silently accepting any chain.

12. **Static client random.** Replace the hardcoded 32-byte test vector in
    `tls13_connect_io_with_config` with `random_bytes(32)`.

### Priority 4 — Resumption

13. **PSK / NewSessionTicket.** Receive and cache session tickets;
    implement `pre_shared_key` extension in ClientHello and PSK branch in
    `tls13_early_secret`.

14. **0-RTT early data.** Depends on PSK.  Low priority; skip for initial
    browser path.

### Priority 5 — Post-quantum

15. **X25519MLKEM768.** Wire ML-KEM-768 once the PQC primitive lands.
    Design is covered in `doc/04_architecture/pqc_hybrid_kex_design.md`.

### Priority 6 — Server-side TLS

16. **`tls13_accept` state machine.** Needed for SimpleOS HTTPS server,
    local development server, and any service that initiates TLS toward
    a client.

---

## 7. References

- RFC 8446 — The Transport Layer Security (TLS) Protocol Version 1.3
- RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
- RFC 7748 — Elliptic Curves for Diffie-Hellman Key Agreement (X25519)
- RFC 8032 — Edwards-Curve Digital Signature Algorithm (EdDSA / Ed25519)
- RFC 8017 — PKCS #1: RSA Cryptography Specifications Version 2.2 (RSA-PSS)
- RFC 5280 — Internet X.509 Public Key Infrastructure Certificate
- RFC 8410 — Algorithm Identifiers for Ed25519 in X.509
- draft-ietf-tls-hybrid-design — Hybrid Key Exchange in TLS 1.3 (PQ KEX)
- `doc/04_architecture/pqc_hybrid_kex_design.md` — PQC roadmap for this repo
- `doc/04_architecture/ssh_algorithm_catalog.md` — SSH sibling implementation

---

## 8. In-Tree Files Surveyed

| File | LOC | Role |
|---|---|---|
| `src/os/tls13/mod.spl` | 11 | Module root / re-exports |
| `src/os/tls13/tls13.spl` | 1,247 | Client handshake state machine, send/recv/close |
| `src/os/tls13/handshake13.spl` | 627 | Wire-format encoder/decoder (pure Simple) |
| `src/os/tls13/record13.spl` | 365 | AEAD record layer (AES-128-GCM) |
| `src/os/tls13/key_schedule.spl` | 179 | RFC 8446 §7.1 key schedule |
| `src/os/tls13/hkdf.spl` | 301 | HKDF (RFC 5869, SHA-256) + Expand-Label |
| `src/os/tls13/transcript.spl` | 55 | Running SHA-256 transcript hash |
| `src/os/tls13/cert_verify.spl` | 711 | X.509 DER parse + signature verification |
| `src/os/tls13/test_server_config.spl` | 122 | Test fixture only |
| **Total** | **3,618** | |
| `src/os/crypto/aes128_gcm.spl` | 620 | AES-128-GCM (used by record13) |
| `src/os/crypto/aes_gcm.spl` | ~200+ | AES-256-GCM (not wired in TLS) |
| `src/os/crypto/chacha20_poly1305.spl` | — | ChaCha20-Poly1305 (not wired in TLS) |
| `src/os/crypto/curve25519.spl` | — | X25519 ECDHE |
| `src/os/crypto/ed25519.spl` | ~840 | Ed25519 sign/verify |
| `src/os/crypto/ecdsa_p256.spl` | — | ECDSA-P256 (not wired in TLS cert dispatch) |
| `src/os/crypto/sha256.spl` | — | SHA-256 + HMAC-SHA-256 |
| `src/os/crypto/sha512.spl` | — | SHA-512 (SHA-384 truncation available) |
