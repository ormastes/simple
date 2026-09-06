# TLS 1.3 Phase 2 Backlog

## Context

### Phase 1 status summary

Phase 1 shipped a complete, pure-Simple TLS 1.3 client state machine in `src/os/tls13/`
(9 files, ~65 KB). It covers the full RFC 8446 client handshake path: X25519 key
exchange, AES-128-GCM record layer (AEAD, sequence-number nonce), SHA-256
transcript/HKDF key schedule, Ed25519-only certificate verification (DER parser +
`ed25519_verify`), and a client Finished MAC. The implementation is baremetal-safe
(no allocator beyond `[u8]` push), tested with unit tests booted under QEMU and a
side-by-side system test against a live `rustls` server. The source is shipped clean:
zero TODOs, FIXMEs, or Phase-2 markers remain inline.

### Where the line was drawn and why

The single cipher suite offered in `ClientHello` is hardcoded to `TLS_AES_128_GCM_SHA256`
(0x1301). Certificate verification is Ed25519-only (OID `1.3.101.112`). No PSK
extensions are sent, no `CertificateRequest` handling exists, and no TLS 1.2 record
layer is present. These constraints kept Phase 1 self-contained and auditable, but
they limit interoperability to servers that have issued Ed25519 certificates — a small
minority in practice.

---

## Deferred capabilities

### 1. RSA-PSS Signatures (`rsa_pss_rsae_sha256`, `rsa_pss_rsae_sha384`, `rsa_pss_rsae_sha512`)

**What:** TLS 1.3 uses RSA-PSS exclusively for RSA-keyed certificate signatures
(RFC 8446 §4.2.3). The handshake `signature_algorithms` extension must advertise
`rsa_pss_rsae_sha{256,384,512}`; `cert_verify.spl` must parse the RSA DER
subjectPublicKeyInfo (`rsaEncryption` OID 1.2.840.113549.1.1.1) and dispatch to
RSA-PSS verification instead of Ed25519.

**Why it matters:** The overwhelming majority of public CAs (Let's Encrypt, DigiCert,
Sectigo, etc.) issue RSA-2048 or RSA-4096 certificates. Phase 1 cannot verify these,
so it cannot complete a handshake with ~95% of real-world HTTPS servers. RSA-PSS is
the highest-leverage single addition.

**FFI status:** `rt_rsa_sha256_verify` and `rt_rsa_sha512_verify` exist in
`src/lib/nogc_sync_mut/io/signature_ffi.spl` and are registered in
`runtime_symbols.rs`. However, these are PKCS#1-v1.5 style; RSA-PSS requires a
new extern `rt_rsa_pss_sha256_verify` (and `..._sha384`, `..._sha512`) — none
currently exist. The Rust runtime side must also implement them (ring or RustCrypto
`rsa` crate).

**Estimated effort:** M

**Dependencies:** new `rt_rsa_pss_sha{256,384,512}_verify` externs in Rust runtime;
DER parser extension in `cert_verify.spl` for `rsaEncryption` OID; updated
`signature_algorithms` extension in `build_client_hello_bytes` (handshake13.spl line
~247 area).

**Blockers:** None architectural — work is additive to existing cert_verify + FFI
layer.

---

### 2. TLS 1.2 fallback

**What:** A subset of servers (internal corporate infrastructure, embedded devices,
old middleware) do not support TLS 1.3. A TLS 1.2 client path requires a separate
record layer (CBC-mode with HMAC, or RC4/AES-CTR for stream ciphers), a separate key
schedule (PRF based on HMAC-SHA{256,384} instead of HKDF), and a different handshake
message structure (ServerKeyExchange, separate ChangeCipherSpec). Downgrade protection
must use the RFC 8446 §4.1.3 sentinel bytes in the ServerHello random field.

**Why it matters:** Without this, the client must abort on any server that negotiates
down from 1.3. Most consumer-facing servers have dropped 1.2-only, but internal
tooling and some API gateways still require it.

**Estimated effort:** L

**Dependencies:** new `record12.spl` (CBC+HMAC or GCM variant), new
`key_schedule12.spl` (PRF-based), cipher suite negotiation logic in handshake
(currently hardcoded to a single 1.3 suite), downgrade sentinel check.

**Blockers:** Largest scope of any deferred item; should follow RSA-PSS (which unblocks
most servers without needing 1.2 at all).

---

### 3. Client certificates (mTLS)

**What:** When a server sends a `CertificateRequest` message (handshake type 13),
the client must respond with its own `Certificate` chain followed by a
`CertificateVerify` signed with the client's private key. This requires local PKCS#8
key storage, parsing of `CertificateRequest` extensions (`signature_algorithms`,
`certificate_authorities`), and client-side signing using the available key type
(Ed25519 or RSA-PSS).

**Why it matters:** Required for mutually-authenticated API endpoints (service-to-service
mTLS in microservice meshes, some cloud provider APIs, SSH-over-TLS-like setups).
Phase 1 silently ignores `CertificateRequest` — a server requiring mTLS will abort.

**Estimated effort:** M

**Dependencies:** RSA-PSS (item 1) if RSA client keys are needed; local cert/key
storage interface (PKCS#8 DER reader); `parse_certificate_request` function in
`handshake13.spl`; client CertificateVerify builder (context string differs from
server: "TLS 1.3, client CertificateVerify").

**Blockers:** None if Ed25519 client certs only; depends on item 1 if RSA client keys
are required.

---

### 4. 0-RTT / PSK resumption

**What:** TLS 1.3 session resumption uses Pre-Shared Keys delivered via
`NewSessionTicket` (handshake type 4) after the initial handshake completes. On
reconnect the client sends the ticket in a `pre_shared_key` extension, and the key
schedule derives a resumption-master-secret–based `binder` instead of a DHE shared
secret, reducing the handshake to 1-RTT. 0-RTT (early data) additionally sends
application data in the first flight using the `early_traffic_secret`.

**Why it matters:** Eliminates one round-trip on reconnection — significant for
latency-sensitive applications (browser page loads, API clients making many short
connections). The key schedule already derives `resumption_master_secret` as part of
`master_secret` derivation, so the cryptographic foundation is partially present.

**Estimated effort:** M

**Security caveats:** 0-RTT early data has no forward secrecy and is vulnerable to
replay attacks; it must only be used for idempotent requests (RFC 8446 §8). PSK
resumption without early data (1-RTT) has no replay risk but requires ticket storage
with expiry enforcement.

**Dependencies:** `NewSessionTicket` parser (currently not handled — message is
silently consumed); ticket storage interface (in-memory or persistent); `early_data`
extension in `ClientHello`; resumption key schedule branch in `key_schedule.spl`
(`res_binder_key`, `early_traffic_secret` labels).

**Blockers:** None architectural; depends on item 1 (RSA-PSS) only if the server uses
RSA in the initial handshake whose ticket is being resumed (which affects cert verify,
not PSK path itself).

---

## Server-side TLS 1.3

Server-side TLS is not in scope for Phase 2. Phase 1 is client-only; the state
machine in `tls13.spl` starts with `build_client_hello_bytes` and processes
server-initiated messages only. A server path would need an `accept`-side handshake
entry point (ServerHello builder, EncryptedExtensions, Certificate/CertificateVerify
sender, Finished verifier). The `key_schedule.spl` module is symmetric and would be
reused as-is; `record13.spl` encrypt/decrypt are also reusable. The server state
machine is a separate design effort; suggest treating it as a Phase 3 item unless
SimpleOS needs to terminate TLS connections itself.

---

## Recommended order of implementation

Priority ordered by user-facing value (most real servers unblocked first):

1. **RSA-PSS signatures** — unblocks ~95% of real-world servers; all other items
   are moot if the client can't complete a handshake with Let's Encrypt certs.
2. **PSK resumption (1-RTT only, no early data)** — latency win on reconnects; builds
   on existing key schedule with no new cryptographic primitives required.
3. **Client certificates (mTLS)** — niche but additive to Phase 1 cert_verify
   infrastructure; unblocks service-mesh and API gateway use cases.
4. **TLS 1.2 fallback** — largest implementation surface, diminishing real-world
   returns (most servers support 1.3 by 2026); implement only if a specific target
   server requires it.

---

## Open questions

1. **RSA-PSS extern implementation:** Does the Rust runtime use `ring` or `RustCrypto/rsa`?
   Affects which crate provides `rsa_pss_rsae_sha*` and whether baremetal (no_std)
   target is supported.
2. **Ticket storage interface:** For PSK resumption, where should session tickets
   live? In-memory (lost on reboot) or a VFS-backed store? Needs user decision
   before designing the resumption path.
3. **mTLS key provisioning:** How are client private keys supplied to the TLS layer?
   A hardcoded path, a capability handle, or a runtime call? The PKCS#8 DER reader
   scope depends on this.
4. **0-RTT gate:** Should the implementation ever send early data, or implement
   1-RTT PSK only? 0-RTT adds significant complexity (replay defense) for marginal
   latency gain versus 1-RTT PSK.
5. **Server-side TLS timeline:** Is SimpleOS expected to terminate TLS (e.g., for
   the browser platform's HTTPS server)? If yes, server-side may need to move into
   Phase 2.

---

## Out-of-scope for Phase 2 (Phase 3+)

- **RSA-PKCS1-v1.5 signatures** — deprecated and forbidden in TLS 1.3 (RFC 8446
  §4.2.3); no implementation value for 1.3-only client.
- **DSA / non-P-256 ECDSA** — low deployment, adds DER complexity; Phase 3 if needed.
- **ChaCha20-Poly1305** (`TLS_CHACHA20_POLY1305_SHA256`, 0x1303) — not present in
  Phase 1; no ChaCha implementation exists anywhere in `src/os/tls13/` or `src/os/crypto/`.
  Would require new cipher primitive before the TLS suite can offer it.
- **Export restrictions / weak cipher suites** — explicitly out of scope.
- **Post-quantum (ML-KEM/Kyber, X25519Kyber768)** — Phase 3+; no RFC has finalized
  the TLS extension format as of April 2026.
