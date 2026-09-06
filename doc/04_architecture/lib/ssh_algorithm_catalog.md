# SSH Algorithm Catalog

**Status:** Design document — no code changes.
**Scope:** `src/os/apps/sshd/` SSH server algorithm negotiation library.
**Date:** 2026-05-01

---

## 1. Goal

An SSH algorithm catalog is the ordered list of cryptographic identifiers a server advertises in
`SSH_MSG_KEXINIT` across four independently negotiated categories: key exchange (kex), server host
key signing, bulk-data encryption (cipher), and message authentication (MAC). Per RFC 4253 the
client and server each send their preference lists; the winning algorithm in each category is the
first name in the server's list that also appears in the client's list. Ordering from newest to
oldest is therefore security policy: a modern client picks the strongest shared algorithm, while a
legacy client falls through to an older but still-acceptable fallback without a connection failure.
This catalog defines which algorithms the Simple SSH server (`src/os/apps/sshd/`) should implement,
in which priority order they should be advertised, and what the current implementation status of
each entry is.

---

## 2. Algorithm Categories (SSH-2 Negotiation)

SSH-2 (RFC 4253) negotiates these categories independently via `SSH_MSG_KEXINIT`:

| Category | KEXINIT field | Notes |
|---|---|---|
| Key exchange | `kex_algorithms` | Diffie-Hellman or ECDH; derives shared secret and exchange hash |
| Host key signing | `server_host_key_algorithms` | Authenticates the server to the client |
| Cipher C→S | `encryption_algorithms_client_to_server` | Bulk encryption, one direction |
| Cipher S→C | `encryption_algorithms_server_to_client` | Bulk encryption, other direction |
| MAC C→S | `mac_algorithms_client_to_server` | Integrity; irrelevant when cipher is AEAD |
| MAC S→C | `mac_algorithms_server_to_client` | Integrity; irrelevant when cipher is AEAD |
| Compression | `compression_algorithms_*` | Out of scope — explicitly disabled (see §6) |

For AEAD ciphers (`chacha20-poly1305@openssh.com`, `aes*-gcm@openssh.com`) the cipher itself
provides authentication; the MAC list is negotiated to `none` and is never used.

---

## 3. The Catalog — Modern to Legacy

### 3.1 KEX Algorithms

| Algorithm | RFC | Status | Primitive | SSH wire status |
|---|---|---|---|---|
| `sntrup761x25519-sha512@openssh.com` | IETF draft | PQ-hybrid (modern) | sntrup761 + curve25519 + sha512 | curve25519 ✓; sntrup761 ✗ missing |
| `curve25519-sha256` | RFC 8731 | Modern | X25519 + SHA-256 | **Fully wired** (`ssh_kex.spl`) |
| `curve25519-sha256@libssh.org` | (alias) | Modern | Same as above | **Fully wired** (same handler) |
| `ecdh-sha2-nistp256` | RFC 5656 | Modern | ECDH P-256 + SHA-256 | ecdsa_p256.spl ✓; SSH ECDH wrapper ✗ missing |
| `ecdh-sha2-nistp384` | RFC 5656 | Modern | ECDH P-384 + SHA-384 | primitive ✗ not implemented |
| `ecdh-sha2-nistp521` | RFC 5656 | Modern | ECDH P-521 + SHA-512 | primitive ✗ not implemented |
| `diffie-hellman-group14-sha256` | RFC 8268 | Acceptable | 2048-bit MODP DH + SHA-256 | primitive ✗ not implemented |
| `diffie-hellman-group16-sha512` | RFC 8268 | Acceptable | 4096-bit MODP DH + SHA-512 | primitive ✗ not implemented |
| `diffie-hellman-group-exchange-sha256` | RFC 4419 | Legacy | DH group exchange + SHA-256 | ✗ not implemented |
| `diffie-hellman-group14-sha1` | RFC 4253 | INSECURE (SHA-1) | 2048-bit MODP DH + SHA-1 | Do not implement |
| `diffie-hellman-group1-sha1` | RFC 4253 | INSECURE (768-bit) | DH group 1 | Do not implement |

**Current server advertisement** (from `_push_server_kex_algorithms` in `ssh_kex.spl`):
```
curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com
```
Only `curve25519-sha256` is a real KEX; the others are capability flags.

### 3.2 Host Key Algorithms

| Algorithm | RFC | Status | Primitive | SSH wire status |
|---|---|---|---|---|
| `ssh-ed25519` | RFC 8709 | Modern | Ed25519 | ✓ wired — **broken interop** (see §5.1) |
| `ssh-ed25519-cert-v01@openssh.com` | OpenSSH cert | Modern | Ed25519 + OpenSSH cert format | `HostCertificateSet` struct present; cert loading path ✓ |
| `ecdsa-sha2-nistp256` | RFC 5656 | Modern | ECDSA P-256 + SHA-256 | **Fully wired** — signing + blob builder in `ssh_kex.spl` |
| `ecdsa-sha2-nistp384` | RFC 5656 | Modern | ECDSA P-384 + SHA-384 | primitive ✗ not implemented |
| `ecdsa-sha2-nistp521` | RFC 5656 | Modern | ECDSA P-521 + SHA-512 | primitive ✗ not implemented |
| `rsa-sha2-512` | RFC 8332 | Acceptable | RSA + SHA-512 | **Fully wired** (`rsa_sha512_sign_with_backend`) |
| `rsa-sha2-256` | RFC 8332 | Acceptable | RSA + SHA-256 | **Fully wired** (`rsa_sha256_sign_with_backend`) |
| `rsa-sha2-256-cert-v01@openssh.com` | OpenSSH cert | Acceptable | RSA-SHA256 + cert | cert struct present; loading path ✓ |
| `rsa-sha2-512-cert-v01@openssh.com` | OpenSSH cert | Acceptable | RSA-SHA512 + cert | cert struct present; loading path ✓ |
| `ssh-rsa` | RFC 4253 | LEGACY (SHA-1) | RSA + SHA-1 | Do not implement — RFC 8332 supersedes |
| `ssh-dss` | RFC 4253 | INSECURE (1024-bit DSA) | DSA-SHA1 | Do not implement |

**Current server advertisement** (from `host_key_set_advertised_algorithms` in `ssh_kex.spl`):
```
ssh-ed25519[,rsa-sha2-256,rsa-sha2-512][,ecdsa-sha2-nistp256]
```
Adapts dynamically to which keys are loaded. Priority: ed25519, then RSA-SHA2 pair, then ECDSA-P256.

### 3.3 Cipher Algorithms

| Algorithm | RFC | Status | Primitive | SSH wire status |
|---|---|---|---|---|
| `chacha20-poly1305@openssh.com` | OpenSSH | Modern AEAD | ChaCha20-Poly1305 | **Fully wired** (`ssh_cipher.spl` `CipherMode.Chacha20Poly1305`) |
| `aes256-gcm@openssh.com` | RFC 5647-style | Modern AEAD | AES-256-GCM | **Fully wired** (`ssh_cipher.spl` `CipherMode.Aes256Gcm`) |
| `aes128-gcm@openssh.com` | RFC 5647-style | Modern AEAD | AES-128-GCM | **Wired in KEXINIT advertisement**; `aes128_gcm.spl` primitive present; cipher dispatch uses AES-256 path — needs routing |
| `aes256-ctr` | RFC 4344 | Acceptable | AES-256-CTR + separate MAC | `_aes256_ctr_crypt` helper fully implemented in `ssh_cipher.spl`; `ssh_encrypt_packet_aes_ctr_etm` / `ssh_decrypt_packet_aes_ctr_etm` present; not yet advertised |
| `aes192-ctr` | RFC 4344 | Acceptable | AES-192-CTR | primitive ✗ not implemented |
| `aes128-ctr` | RFC 4344 | Acceptable | AES-128-CTR | primitive ✗ not implemented |
| `aes256-cbc` | RFC 4253 | LEGACY | AES-256-CBC | Do not implement |
| `3des-cbc` | RFC 4253 | INSECURE | 3DES | Do not implement |
| `arcfour256/128` | RFC 4253 | BROKEN | RC4 | Do not implement |
| `blowfish-cbc` | RFC 4253 | LEGACY | Blowfish | Do not implement |

**Current server advertisement** (from `ssh_build_kexinit_for_host_keys` in `ssh_kex.spl`):
```
aes128-gcm@openssh.com
```
Both C→S and S→C advertise only `aes128-gcm@openssh.com` in the non-cert path. The cert path
advertises `aes128-gcm@openssh.com` as well. Notably `aes256-gcm@openssh.com` is **not advertised
in KEXINIT** even though the AES-256-GCM encrypt/decrypt path is the one actually invoked by
`SshCipher.activate()`.

### 3.4 MAC Algorithms

| Algorithm | RFC | Status | Primitive | SSH wire status |
|---|---|---|---|---|
| `hmac-sha2-256-etm@openssh.com` | OpenSSH | Modern EtM | HMAC-SHA-256 | **Fully wired** (`ssh_mac.spl`) |
| `hmac-sha2-512-etm@openssh.com` | OpenSSH | Modern EtM | HMAC-SHA-512 | **Fully wired** (`ssh_mac.spl`) |
| `hmac-sha2-256` | RFC 6668 | Acceptable | HMAC-SHA-256 | primitive ✓; not wired in `ssh_mac_compute` dispatch |
| `hmac-sha2-512` | RFC 6668 | Acceptable | HMAC-SHA-512 | primitive ✓; not wired in `ssh_mac_compute` dispatch |
| `hmac-sha1-etm@openssh.com` | OpenSSH | LEGACY | HMAC-SHA-1 EtM | Do not implement |
| `hmac-md5` | RFC 4253 | BROKEN | HMAC-MD5 | Do not implement |

**Current server advertisement** (cert path in `ssh_kex.spl`):
```
hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none
```
The non-cert (baremetal) KEXINIT path hard-codes `none` for both MAC slots because AEAD ciphers
are assumed. The EtM algorithms are only advertised when certs are in use.

---

## 4. Server-Recommended Preference Order

The following is the target preference list for a modern Simple SSH server. All entries are ordered
modern → acceptable. Insecure and legacy entries are omitted.

```
KEX:
  curve25519-sha256
  curve25519-sha256@libssh.org      (alias, same handler)
  ecdh-sha2-nistp256                (needs SSH ECDH wrapper — P-256 primitive exists)
  diffie-hellman-group16-sha512     (needs MODP DH primitive)
  diffie-hellman-group14-sha256     (needs MODP DH primitive)
  [sntrup761x25519-sha512@openssh.com — future, when sntrup761 primitive lands]

HostKey:
  ssh-ed25519                       (wired but interop broken — see §5.1)
  ssh-ed25519-cert-v01@openssh.com  (cert format present)
  ecdsa-sha2-nistp256               (fully wired)
  rsa-sha2-512                      (fully wired)
  rsa-sha2-256                      (fully wired)

Cipher:
  chacha20-poly1305@openssh.com     (fully wired)
  aes256-gcm@openssh.com            (wired but not yet advertised — see §5.2)
  aes128-gcm@openssh.com            (advertised; primitive present; dispatch routing gap)
  aes256-ctr                        (helpers wired; not yet advertised)
  aes128-ctr                        (needs primitive)

MAC (only relevant with aes*-ctr ciphers):
  hmac-sha2-256-etm@openssh.com     (fully wired)
  hmac-sha2-512-etm@openssh.com     (fully wired)
  hmac-sha2-256                     (primitive ready; dispatch gap)
  hmac-sha2-512                     (primitive ready; dispatch gap)
```

---

## 5. What's Wired, What's Blocked

### 5.1 Full Status Matrix

| Algorithm | KEX | HostKey | Cipher | MAC | Notes |
|---|---|---|---|---|---|
| curve25519-sha256 | ✓ | — | — | — | Fully wired in `ssh_kex.spl` |
| ssh-ed25519 | — | ⚠ | — | — | Wired but Ed25519 sign/verify has RFC 8032 vector mismatch (see bug doc) |
| ecdsa-sha2-nistp256 | — | ✓ | — | — | Fully wired: PKCS#8 parse + sign + blob builder |
| rsa-sha2-256 | — | ✓ | — | — | Fully wired via `rsa_sha256_sign_with_backend` |
| rsa-sha2-512 | — | ✓ | — | — | Fully wired via `rsa_sha512_sign_with_backend` |
| aes256-gcm@openssh.com | — | — | ⚠ | — | Encrypt/decrypt implemented; not advertised in KEXINIT |
| aes128-gcm@openssh.com | — | — | ⚠ | — | Advertised; `aes128_gcm.spl` present; cipher dispatch routes to AES-256 path |
| chacha20-poly1305@openssh.com | — | — | ✓ | — | Fully wired in `ssh_cipher.spl` |
| aes256-ctr | — | — | ⚠ | — | `_aes256_ctr_crypt` + EtM helpers implemented; not advertised |
| hmac-sha2-256-etm@openssh.com | — | — | — | ✓ | Fully wired in `ssh_mac.spl` |
| hmac-sha2-512-etm@openssh.com | — | — | — | ✓ | Fully wired in `ssh_mac.spl` |
| hmac-sha2-256 | — | — | — | ⚠ | Primitive ready; `ssh_mac_compute` dispatch doesn't handle non-EtM form |
| hmac-sha2-512 | — | — | — | ⚠ | Primitive ready; same gap as above |
| ecdh-sha2-nistp256 (KEX) | ✗ | — | — | — | P-256 scalar multiply exists; ECDH key exchange flow missing |
| diffie-hellman-group14-sha256 | ✗ | — | — | — | MODP DH primitive missing |
| diffie-hellman-group16-sha512 | ✗ | — | — | — | MODP DH primitive missing |
| sntrup761x25519 | ✗ | — | — | — | sntrup761 missing; curve25519 half ready |
| aes128-ctr | — | — | ✗ | — | AES-128 CTR mode not implemented |
| ssh-ed25519-cert | — | ⚠ | — | — | Cert struct + loading present; blocked on Ed25519 interop bug |

Legend: ✓ shippable / ⚠ needs fix or routing / ✗ missing primitive or wrapper

### 5.2 Known Inconsistencies Found During Survey

**KEXINIT advertises `aes128-gcm` but activates AES-256:**
`ssh_build_kexinit_for_host_keys` hard-codes `aes128-gcm@openssh.com` in the cipher fields of the
non-cert KEXINIT (see `_push_gcm_cipher_pair` which emits the literal `aes128-gcm@openssh.com`).
However `SshCipher.activate()` always selects `CipherMode.Aes256Gcm`, which calls
`aes256_gcm_encrypt`/`aes256_gcm_decrypt`. The server negotiates AES-128 but uses AES-256 keys.
This is an advertisement/dispatch mismatch.

**`aes256-gcm@openssh.com` is never advertised:**
Despite being the cipher that `SshCipher.activate()` actually uses, `aes256-gcm@openssh.com` never
appears in the KEXINIT output in the non-cert path. `_push_aes256_gcm_openssh` exists in
`ssh_kex.spl` but is not called from `ssh_build_kexinit_for_host_keys`.

**`aes256-ctr` + EtM is silently implemented but not advertised:**
`ssh_encrypt_packet_aes_ctr_etm` and `ssh_decrypt_packet_aes_ctr_etm` are fully implemented in
`ssh_cipher.spl`, but `aes256-ctr` is not listed in any KEXINIT builder. The code is dead until
the cipher enum is extended and the advertisement is added.

### 5.3 Priority Order for Next Implementation Steps

1. **Fix KEXINIT advertisement mismatch** — advertise `aes256-gcm@openssh.com` as first cipher
   preference, or route `aes128-gcm@openssh.com` negotiations to `aes128_gcm.spl`.
   Files: `src/os/apps/sshd/ssh_kex.spl` (`_push_server_kex_algorithms`, `_push_gcm_cipher_pair`).

2. **Fix Ed25519 interop** — `ssh-ed25519` is wired but produces signatures that fail RFC 8032 test
   vectors. Without this fix `ssh-ed25519` cannot be reliably used as the preferred host key type.
   File: `src/os/crypto/ed25519.spl`; see
   `doc/08_tracking/bug/ed25519_rfc8032_vector_mismatch_2026-05-01.md`.

3. **Advertise and activate `aes256-ctr` + `hmac-sha2-256-etm`** — the canonical non-AEAD fallback
   combo for legacy peers. The cipher helpers exist; requires extending `CipherMode` enum and
   updating `ssh_build_kexinit_for_host_keys`.
   Files: `src/os/apps/sshd/ssh_cipher.spl`, `src/os/apps/sshd/ssh_kex.spl`.

4. **`ecdh-sha2-nistp256` KEX** — add ECDH key exchange flow (keygen + shared-secret computation
   using P-256 scalar multiply). The signing primitive (`ecdsa_p256.spl`) is ready; the exchange
   hash and wire protocol for ECDH need a new `ssh_kex_ecdh_p256_*` set of functions.
   Files: `src/os/apps/sshd/ssh_kex.spl`, `src/os/crypto/ecdsa_p256.spl`.

5. **Wire `hmac-sha2-256` and `hmac-sha2-512` (non-EtM)** — add dispatch cases to
   `ssh_mac_compute` and `ssh_mac_len` in `src/os/apps/sshd/ssh_mac.spl`. Needed for legacy
   `aes256-ctr` with non-EtM MAC clients.

6. **MODP DH group14/group16** — requires a big-integer modular exponentiation primitive (not in
   tree). New file `src/os/crypto/dh_modp.spl` needed before KEX can be wired.

7. **`sntrup761x25519`** — PQ hybrid; requires `sntrup761` KEM (not in tree). Long-term future
   work; curve25519 half is already present.

---

## 6. Out of Scope

The following are explicitly excluded and should not be implemented:

- **All `*-sha1` algorithms** — `diffie-hellman-group14-sha1`, `diffie-hellman-group1-sha1`,
  `hmac-sha1`, `hmac-sha1-etm@openssh.com`: SHA-1 is cryptographically broken for signature use.
- **`ssh-rsa`** (RFC 4253, uses SHA-1 for signatures) — superseded by `rsa-sha2-256` and
  `rsa-sha2-512` (RFC 8332). Any RSA host key should only be advertised under the SHA-2 names.
- **`ssh-dss`** (DSA-SHA1, 1024-bit) — INSECURE. 1024-bit DSA has been deprecated by NIST and
  removed from OpenSSH 7.0.
- **`3des-cbc`, `blowfish-cbc`, `aes*-cbc`** — CBC mode with SSH is vulnerable to Lucky13 and
  related timing attacks. Not worth the interop maintenance burden.
- **`arcfour256`, `arcfour128`, `arcfour`** — RC4 is cryptographically broken (BEAST, RC4 biases).
  RFC 8758 prohibits RC4 in TLS; same applies here.
- **`hmac-md5`, `hmac-md5-96`** — MD5 is cryptographically broken.
- **Compression** — `zlib` and `zlib@openssh.com` are disabled. Compression before encryption
  enables CRIME/BREACH-style chosen-plaintext attacks. Both C→S and S→C compression fields
  advertise `none` only.

---

## 7. References

- **RFC 4253** — The Secure Shell (SSH) Transport Layer Protocol
- **RFC 4344** — The Secure Shell (SSH) Transport Layer Encryption Modes (AES-CTR)
- **RFC 4419** — Diffie-Hellman Group Exchange for the Secure Shell (SSH) Transport Layer Protocol
- **RFC 5647** — AES Galois Counter Mode for the Secure Shell Transport Layer Protocol
- **RFC 5656** — Elliptic Curve Algorithm Integration in the Secure Shell Transport Layer
- **RFC 6668** — SHA-2 Data Integrity Verification for the Secure Shell (SSH) Transport Layer
- **RFC 8268** — More Modular Exponentiation (MODP) Diffie-Hellman (DH) Key Exchange Groups
- **RFC 8332** — Use of RSA Keys with SHA-256 and SHA-512 in the Secure Shell Protocol
- **RFC 8709** — Ed25519 and Ed448 Public Key Algorithms for the Secure Shell (SSH) Protocol
- **RFC 8731** — Secure Shell (SSH) Key Exchange Method Using Curve25519 and Curve448
- **OpenSSH `chacha20-poly1305@openssh.com`** — chacha-poly@openssh.com format spec (two-key
  construction with separate length and payload keys); note: Simple's current implementation uses a
  single key / simplified variant.
- **OpenSSH `*-etm@openssh.com` MACs** — Encrypt-then-MAC construction, extends RFC 6668.
- `man ssh -Q kex`, `man ssh -Q cipher`, `man ssh -Q mac`, `man ssh -Q key` — OpenSSH catalog
  membership on any current OpenSSH host.

---

## 8. Cross-References

| Path | Relevance |
|---|---|
| `src/os/apps/sshd/ssh_kex.spl` | KEX state machine, KEXINIT builder, host key blob builders, multi-algorithm signing dispatch |
| `src/os/apps/sshd/ssh_cipher.spl` | AES-256-GCM, ChaCha20-Poly1305, AES-256-CTR encrypt/decrypt |
| `src/os/apps/sshd/ssh_mac.spl` | HMAC-SHA-256-EtM, HMAC-SHA-512-EtM compute and verify |
| `src/os/apps/sshd/ssh_transport.spl` | Transport state machine wiring cipher and MAC layers |
| `src/os/apps/sshd/host_key_loader.spl` | Loads `HostKeySet` from disk |
| `src/os/crypto/curve25519.spl` | X25519 scalar multiply (KEX primitive) |
| `src/os/crypto/ed25519.spl` | Ed25519 sign/verify (host key primitive — interop bug active) |
| `src/os/crypto/ecdsa_p256.spl` | ECDSA P-256 sign + `fixed64_to_ssh_mpint_pair` formatter |
| `src/os/crypto/rsa.spl` | RSA sign with SHA-256 and SHA-512 backends |
| `src/os/crypto/aes_gcm.spl` | AES-256-GCM encrypt/decrypt |
| `src/os/crypto/aes128_gcm.spl` | AES-128-GCM encrypt/decrypt (primitive present; not dispatched) |
| `src/os/crypto/chacha20_poly1305.spl` | ChaCha20-Poly1305 AEAD |
| `src/os/crypto/sha256.spl` | SHA-256 and HMAC-SHA-256 |
| `src/os/crypto/sha512.spl` | SHA-512 (used for HMAC-SHA-512) |
| `doc/08_tracking/bug/ed25519_rfc8032_vector_mismatch_2026-05-01.md` | Ed25519 interop blocker for `ssh-ed25519` host key |
