# PQC Hybrid Key Exchange Design

**`X25519MLKEM768` (TLS 1.3) and `sntrup761x25519-sha512` (SSH)**

Status: Design doc — primitives not yet implemented.
Date: 2026-05-01
Authors: architecture team

---

## 1. Goal

Post-quantum hybrid key exchange is the modern path to forward security against future quantum
attackers capable of running Shor's algorithm. Both the IETF (TLS 1.3) and OpenSSH have settled
on hybrid constructions that run a classical ECDH share in parallel with a post-quantum KEM share
and combine the two raw secrets into a single handshake key. The two hybrids differ in the choice
of PQ primitive (ML-KEM-768 vs. sntrup761) and in how the raw secrets are combined (HKDF vs.
SHA-512 hash). Both share X25519 as the classical half, which is already shipped in
`src/os/crypto/curve25519.spl`. This document identifies the gap between what is currently in the
tree and what is needed, proposes a minimal API surface for the new primitives, describes the
hybrid combiner logic mandated by each protocol spec, and maps out integration points in the
existing SSH KEX layer (`src/os/apps/sshd/ssh_kex.spl`) and TLS 1.3 handshake
(`src/os/tls13/handshake13.spl`).

---

## 2. The Two Hybrids and Why They Look Different

### 2.1 `X25519MLKEM768` (TLS 1.3, code point 0x11ec)

Specified by draft-ietf-tls-hybrid-design (IETF TLS WG). The PQ half is ML-KEM-768, defined by
FIPS 203 (the NIST standardization of CRYSTALS-Kyber-768, August 2024). ML-KEM is a
Key Encapsulation Mechanism: the server generates a keypair, sends the public key in the
`key_share` extension of ServerHello (NamedGroup 0x11ec), and the client encapsulates a random
shared secret under that public key and returns the ciphertext. The server decapsulates to
recover the same shared secret. The raw X25519 share runs independently in parallel.

The hybrid shared secret fed into TLS 1.3 HKDF is:

```
tls_dh_input = ML-KEM-768.SharedSecret || X25519.SharedSecret
```

**Order matters: ML-KEM first, X25519 second.** This is the order mandated by the draft spec.
The combined 64-byte value replaces the `(EC)DHE` input to the TLS 1.3 key schedule.

Chrome shipped `X25519MLKEM768` (0x11ec) in Chrome 124 (May 2024), replacing the earlier
`x25519_kyber768_draft00` (0x6399). Firefox shipped it in Firefox 132. Cloudflare has offered it
since 2024-Q3.

The current TLS 1.3 stack in `src/os/tls13/` hardwires X25519 as the single `key_share` group
in ClientHello (`_build_ext_key_share` in `handshake13.spl`). Adding `X25519MLKEM768` requires
sending a concatenated `key_share` entry for NamedGroup 0x11ec rather than 0x001d.

### 2.2 `sntrup761x25519-sha512@openssh.com` (SSH)

Specified in OpenSSH's `PROTOCOL` file (not an RFC). The PQ half is sntrup761, a parameter set
of NTRU Prime (Streamlined NTRU Prime). OpenSSH chose sntrup761 before NIST completed its
selection; it predates FIPS 203 and is not an NIST standard, but it has been the default SSH KEX
algorithm since OpenSSH 9.0 (April 2022).

The hybrid exchange follows standard SSH KEX wire format, then the shared secret derivation is:

```
hash_input = sntrup761.SharedSecret || X25519.SharedSecret
K = SHA-512(hash_input)
```

**Order: sntrup761 first, X25519 second.** SSH does not use a separate KDF step; the 64-byte
SHA-512 output directly becomes the session-level shared secret `K` passed into the SSH key
derivation.

The current SSH KEX layer in `src/os/apps/sshd/ssh_kex.spl` implements
`curve25519-sha256` and `curve25519-sha256@libssh.org`. The algorithm name
`sntrup761x25519-sha512@openssh.com` is not yet in the catalog.

### 2.3 The Common Pattern

Both hybrids share the same structural property: the combined secret is at most as strong as
the strongest individual algorithm. If X25519 is broken by a quantum computer, ML-KEM-768
(or sntrup761) still protects the session key. If the PQ primitive is broken by a classical
cryptanalysis advance, X25519 still protects the session key. The hybrid provides
defense-in-depth at the cost of larger messages and more computation.

---

## 3. Primitive Inventory (Gap Analysis)

Investigation confirmed:

- No PQC primitive of any kind is currently in the Simple tree (no kyber, sntrup, ml_kem,
  dilithium, ntru matches outside vendor directories).
- X25519 ECDH is shipped and tested.
- SHA-512 is shipped in both `src/os/crypto/sha512.spl` and `src/lib/common/crypto/sha512.spl`.
- HKDF is shipped at `src/os/tls13/hkdf.spl`.
- The SSH KEX dispatcher (`src/os/apps/sshd/ssh_kex.spl`) has a clean algorithm dispatch
  pattern for adding new KEX methods.
- The TLS 1.3 handshake (`src/os/tls13/handshake13.spl`) currently hardwires X25519 only.

| Primitive | Status | Canonical location |
|---|---|---|
| X25519 ECDH | shipped | `src/os/crypto/curve25519.spl` |
| SHA-512 | shipped | `src/os/crypto/sha512.spl` |
| HKDF (for TLS 1.3) | shipped | `src/os/tls13/hkdf.spl` |
| ML-KEM-768 keypair | missing | `src/lib/common/pqc/ml_kem_768.spl` (new) |
| ML-KEM-768 encapsulate | missing | same |
| ML-KEM-768 decapsulate | missing | same |
| sntrup761 keypair | missing | `src/lib/common/pqc/sntrup761.spl` (new) |
| sntrup761 encapsulate | missing | same |
| sntrup761 decapsulate | missing | same |
| Hybrid combiner (TLS) | missing | `src/lib/common/pqc/hybrid_kex.spl` (new) |
| Hybrid combiner (SSH) | missing | same |
| ML-DSA-65 sign/verify | missing | out of scope (separate doc) |

---

## 4. Proposed API Surface

The new primitives live under `src/lib/common/pqc/`. They are pure-Simple with no runtime
externs, using only `[u8]` byte slices and the existing `Random` type for key generation.

### 4.1 ML-KEM-768 (`ml_kem_768.spl`)

Key and ciphertext sizes per FIPS 203, Section 7.3 (parameter set k=3):

```simple
# Key and ciphertext container types
class MlKem768PublicKey:
    """ML-KEM-768 encapsulation key (ek). 1184 bytes per FIPS 203."""
    var bytes: [u8]

class MlKem768PrivateKey:
    """ML-KEM-768 decapsulation key (dk). 2400 bytes per FIPS 203."""
    var bytes: [u8]

class MlKem768Ciphertext:
    """ML-KEM-768 ciphertext. 1088 bytes per FIPS 203."""
    var bytes: [u8]

# Key generation
fn ml_kem_768_keypair(rng: Random) -> (MlKem768PublicKey, MlKem768PrivateKey)

# Client-side: encapsulate a random shared secret under the server public key.
# Returns the ciphertext to send and the 32-byte shared secret to keep locally.
fn ml_kem_768_encapsulate(pub: MlKem768PublicKey, rng: Random) -> (MlKem768Ciphertext, [u8])

# Server-side: recover the shared secret from the ciphertext.
# Returns the 32-byte shared secret.
fn ml_kem_768_decapsulate(priv: MlKem768PrivateKey, ct: MlKem768Ciphertext) -> [u8]
```

The ML-KEM internal structure (NTT, module lattice, compression/decompression) follows FIPS 203
verbatim. The NTT operates over Zq where q=3329. The modulus 3329 fits in a u16; all polynomial
coefficients are u16 values. The NTT requires a 256-point transform with precomputed twiddle
factors — the zetas table from FIPS 203 Table 1.

### 4.2 sntrup761 (`sntrup761.spl`)

Key and ciphertext sizes from the NTRU Prime sntrup761 specification and the OpenSSH reference
implementation:

```simple
class Sntrup761PublicKey:
    """sntrup761 public key. 1158 bytes."""
    var bytes: [u8]

class Sntrup761PrivateKey:
    """sntrup761 private key. 1763 bytes."""
    var bytes: [u8]

class Sntrup761Ciphertext:
    """sntrup761 ciphertext. 1039 bytes."""
    var bytes: [u8]

fn sntrup761_keypair(rng: Random) -> (Sntrup761PublicKey, Sntrup761PrivateKey)

# Returns the ciphertext to send and the 32-byte shared secret.
fn sntrup761_encapsulate(pub: Sntrup761PublicKey, rng: Random) -> (Sntrup761Ciphertext, [u8])

# Returns the 32-byte shared secret.
fn sntrup761_decapsulate(priv: Sntrup761PrivateKey, ct: Sntrup761Ciphertext) -> [u8]
```

sntrup761 internals: the polynomial ring is Fq[x]/(x^761 - x - 1) with q=4591. Key generation
produces a random small polynomial f (coefficients in {-1, 0, 1}) and inverts it in Zq. The
constant-time requirement is satisfied by a sorting network (Benes network over polynomial
coefficients) that avoids data-dependent branches. The OpenSSH reference (`crypto_kem/sntrup761/ref/`)
is approximately 1800 lines of C and is the authoritative reference for the Simple port.

### 4.3 Hybrid Combiner (`hybrid_kex.spl`)

The facade wires the two primitives together and implements the protocol-mandated combination
order.

```simple
class HybridPublicKey:
    """Concatenated public keys for a hybrid KEX."""
    var x25519_pub: [u8]     # 32 bytes
    var pq_pub: [u8]         # 1184 bytes (ML-KEM) or 1158 bytes (sntrup761)

class HybridPrivateKey:
    var x25519_priv: [u8]    # 32 bytes
    var pq_priv: [u8]        # 2400 bytes (ML-KEM) or 1763 bytes (sntrup761)

class HybridCiphertext:
    """Concatenated ciphertexts for a hybrid KEX."""
    var x25519_pub: [u8]     # 32 bytes (ephemeral, sent as the classical ciphertext)
    var pq_ct: [u8]          # 1088 bytes (ML-KEM) or 1039 bytes (sntrup761)

# TLS 1.3 X25519MLKEM768 (NamedGroup 0x11ec)
fn x25519_mlkem768_keypair(rng: Random) -> (HybridPublicKey, HybridPrivateKey)
fn x25519_mlkem768_encapsulate(pub: HybridPublicKey, rng: Random) -> (HybridCiphertext, [u8])
fn x25519_mlkem768_decapsulate(priv: HybridPrivateKey, ct: HybridCiphertext) -> [u8]

# SSH sntrup761x25519-sha512@openssh.com
fn sntrup761x25519_keypair(rng: Random) -> (HybridPublicKey, HybridPrivateKey)
fn sntrup761x25519_encapsulate(pub: HybridPublicKey, rng: Random) -> (HybridCiphertext, [u8])
fn sntrup761x25519_decapsulate(priv: HybridPrivateKey, ct: HybridCiphertext) -> [u8]
```

---

## 5. Hybrid Combiner Logic

### 5.1 TLS 1.3 X25519MLKEM768

Mandated by draft-ietf-tls-hybrid-design (as implemented by Chrome, Firefox, Cloudflare):

```
mlkem_secret   = ML-KEM-768.Decapsulate(priv.pq_priv, ct.pq_ct)   # 32 bytes
x25519_secret  = X25519(priv.x25519_priv, ct.x25519_pub)           # 32 bytes
tls_dh_input   = mlkem_secret || x25519_secret                     # 64 bytes
```

The 64-byte `tls_dh_input` replaces the `(EC)DHE` field in the TLS 1.3 key schedule
(`HKDF-Extract` step in `src/os/tls13/key_schedule.spl`). No additional hashing is needed
at the combiner layer — TLS 1.3's HKDF handles derivation.

On the encapsulate side (client sends key_share):

```
(pq_ct, mlkem_secret) = ML-KEM-768.Encapsulate(pub.pq_pub, rng)
x25519_priv_eph       = random_scalar(rng)
x25519_pub_eph        = X25519_base(x25519_priv_eph)
x25519_secret         = X25519(x25519_priv_eph, pub.x25519_pub)
tls_dh_input          = mlkem_secret || x25519_secret
ct = HybridCiphertext { x25519_pub: x25519_pub_eph, pq_ct: pq_ct }
```

### 5.2 SSH sntrup761x25519

Mandated by OpenSSH PROTOCOL (section `sntrup761x25519-sha512@openssh.com`):

```
sntrup_secret  = sntrup761.Decapsulate(priv.pq_priv, ct.pq_ct)    # 32 bytes
x25519_secret  = X25519(priv.x25519_priv, ct.x25519_pub)           # 32 bytes
hash_input     = sntrup_secret || x25519_secret                    # 64 bytes
K              = SHA-512(hash_input)                               # 64 bytes
```

The 64-byte `K` is the SSH shared secret. Unlike TLS 1.3, SSH performs its own hash here rather
than delegating to a KDF. The SHA-512 call uses `src/os/crypto/sha512.spl`.

On the encapsulate side (client sends KEX_ECDH_INIT):

```
(pq_ct, sntrup_secret) = sntrup761.Encapsulate(pub.pq_pub, rng)
x25519_priv_eph        = random_scalar(rng)
x25519_pub_eph         = X25519_base(x25519_priv_eph)
x25519_secret          = X25519(x25519_priv_eph, pub.x25519_pub)
K                      = SHA-512(sntrup_secret || x25519_secret)
```

---

## 6. SSH Integration Plan

The SSH KEX dispatcher in `src/os/apps/sshd/ssh_kex.spl` already has a clean structure.
The `_push_server_kex_algorithms` function builds the comma-separated algorithm list, and
`ssh_kex_compute_shared` handles the shared secret computation. The following changes are needed:

### 6.1 Algorithm Catalog

Add `"sntrup761x25519-sha512@openssh.com"` to the algorithm list in `_push_server_kex_algorithms`.
Per `doc/04_architecture/ssh_algorithm_catalog.md`, this entry should appear before
`curve25519-sha256` in priority order — OpenSSH clients prefer the PQC hybrid when the server
advertises both.

### 6.2 KEX Dispatch

Extend the algorithm dispatch in `ssh_kex.spl` to handle the new algorithm name. When the
negotiated KEX method is `sntrup761x25519-sha512@openssh.com`:

1. **Server keypair generation:** call `sntrup761x25519_keypair` to produce server-side
   `HybridPublicKey` and `HybridPrivateKey`. Serialize as `sntrup761_pub || x25519_pub`
   (1158 + 32 = 1190 bytes) for the SSH_MSG_KEX_ECDH_REPLY public key field.

2. **Client key_share ingestion:** deserialize the client's KEX_ECDH_INIT payload as
   `sntrup761_ct || x25519_pub_eph` (1039 + 32 = 1071 bytes).

3. **Shared secret derivation:** call `sntrup761x25519_decapsulate` to produce `K`.

4. **Exchange hash:** the exchange hash `H` computation in `ssh_kex_compute_exchange_hash`
   remains SHA-256 (unchanged); only `K` changes.

### 6.3 Wire Format Reference

From the OpenSSH PROTOCOL file (KEX_ECDH_INIT / KEX_ECDH_REPLY for the sntrup761 hybrid):

- Client to server (KEX_ECDH_INIT): `Q_C = sntrup761_pubkey || x25519_pubkey` (1190 bytes).
  This is the client's hybrid public key — the server will encapsulate under it.
- Server to client (KEX_ECDH_REPLY): `Q_S = sntrup761_ciphertext || x25519_pubkey_eph`
  (1071 bytes). This is the server's encapsulation result plus ephemeral X25519 share.
- The server role generates the keypair; the client performs encapsulation. This is the
  reverse of the TLS 1.3 role assignment (where the server encapsulates under the client's
  key_share).

### 6.4 Testing

```bash
ssh -o KexAlgorithms=sntrup761x25519-sha512@openssh.com user@server
```

OpenSSH 9.0+ clients default to this algorithm; no flag is needed for modern clients. A
round-trip integration test should verify the full SSH handshake against an OpenSSH client.

---

## 7. TLS 1.3 Integration Plan

The TLS 1.3 stack lives at `src/os/tls13/`. The handshake currently hardwires X25519 (NamedGroup
0x001d) as the sole `key_share` entry.

### 7.1 NamedGroup Constant

Add `0x11ec_u16` as a constant for `X25519MLKEM768`. This code point was assigned by IANA for
the hybrid group (distinct from the older Kyber draft code point 0x6399 which is now obsolete).

### 7.2 key_share Extension

`_build_ext_key_share` in `handshake13.spl` currently writes a single X25519 key share.
To support `X25519MLKEM768`:

1. Serialize the hybrid public key as `x25519_pub || mlkem768_pub` (32 + 1184 = 1216 bytes).
2. Write a `key_share` entry with group=0x11ec and the 1216-byte key_share_data.
3. Clients MAY send both 0x001d (X25519) and 0x11ec (hybrid) to maximize compatibility with
   servers that do not yet support the hybrid.

### 7.3 ServerHello Parsing

`_serverhello_x25519_pub` and `ServerHello13` in `handshake13.spl` currently extract only the
X25519 public key. For 0x11ec, the server's key_share_data is `mlkem_ct || x25519_pub_eph`
(1088 + 32 = 1120 bytes). The parser must extract both fields.

### 7.4 Key Schedule Integration

`key_schedule.spl` receives the `(EC)DHE` input. When the negotiated group is 0x11ec, pass the
64-byte `tls_dh_input = mlkem_secret || x25519_secret` in place of the 32-byte X25519 secret.
The HKDF calls are unchanged — HKDF handles arbitrary-length IKM.

### 7.5 Testing

Cross-check against Cloudflare's CIRCL library (`go-circl/kem/hybrid/x25519mlkem768`) and
against OpenSSL 3.2+ which also implements the 0x11ec code point.

---

## 8. Implementation Difficulty

Honest estimates based on reference implementation sizes:

| Component | Estimate | Notes |
|---|---|---|
| ML-KEM-768 | 2000–3000 lines | FIPS 203 pseudocode is the reference; NTT over Zq=3329 is the hard part |
| sntrup761 | 1500–2500 lines | OpenSSH C reference is ~1800 lines; constant-time sorting network is non-trivial |
| Hybrid combiner | ~150 lines | Trivial once primitives exist |
| SSH wire-up | ~300–500 lines | KEX dispatch, serialization, test |
| TLS 1.3 wire-up | ~400–700 lines | key_share parser, key schedule integration, test |
| **Total** | **~5–10 kLOC** | Multi-week effort; ML-KEM first unblocks both TLS and future use |

**The hardest implementation challenge is constant-time correctness.** Both ML-KEM and sntrup761
have well-known timing side-channel requirements:

- ML-KEM: the rejection sampling loop in key generation and the implicit rejection path in
  decapsulation must not branch on secret data.
- sntrup761: coefficient sorting must use a constant-time comparator network, not `sort()`.

The Simple language currently lacks a `ct_select` or `ct_cmov` primitive. These should be
implemented as simple arithmetic expressions (`b*x + (1-b)*y` where `b` is a 0/1 mask) rather
than branching. If the compiler generates a conditional branch for such expressions, that is a
compiler bug that should be filed.

---

## 9. Phased Implementation Plan

- **Phase A:** ML-KEM-768 primitive. Verify against NIST CAVP KAT vectors (FIPS 203 test
  vectors, available at csrc.nist.gov). This unblocks both TLS 1.3 and future HPKE use.

- **Phase B:** sntrup761 primitive. Verify against OpenSSH KAT vectors from
  `crypto_kem/sntrup761/ref/KAT/`. Port the constant-time sorting network from the C reference.

- **Phase C:** Hybrid combiners (`hybrid_kex.spl`). Round-trip KAT tests for both combinations.
  Cross-check sntrup761x25519 against OpenSSH; cross-check X25519MLKEM768 against CIRCL.

- **Phase D:** SSH KEX wire-up. Integration test: full SSH handshake against OpenSSH 9.x client.

- **Phase E:** TLS 1.3 NamedGroup wire-up. Integration test: TLS 1.3 handshake with a server
  that supports 0x11ec (nginx + OpenSSL 3.2+ or Cloudflare).

Phases A and B are independent and can be parallelized. Phase C depends on both. Phases D and E
each depend only on Phase C.

---

## 10. Out of Scope

The following are explicitly deferred:

- **ML-DSA-65 signing (FIPS 204):** This is a different algorithm family (lattice-based
  signatures). It addresses certificate signing and host key authentication, not key exchange.
  Requires a separate design document.
- **SLH-DSA / SPHINCS+ (FIPS 205):** Hash-based signatures. Low deployment urgency. Deferred.
- **Falcon (NTRU-based signatures):** Not standardized by NIST. Deferred.
- **Kyber-512 / Kyber-1024:** Superseded by FIPS 203. Only ML-KEM-768 maps to the deployed
  TLS code points and OpenSSH algorithms.
- **Other sntrup variants (sntrup653, sntrup857, sntrup953):** OpenSSH ships only sntrup761.
  Implementing other parameter sets provides no interoperability benefit.
- **HPKE (RFC 9180):** The Hybrid Public Key Encryption standard uses ML-KEM as one of its
  optional KEM choices. Implementing ML-KEM-768 as a primitive (Phase A) would allow HPKE
  support later, but HPKE itself is out of scope here.
- **X25519Kyber768Draft00 (0x6399):** The obsolete pre-standardization code point. Chrome and
  Firefox have dropped it. Do not implement.

---

## 11. Test Vector Sources

| Algorithm | Vector source |
|---|---|
| ML-KEM-768 | NIST CAVP post-quantum test vectors at csrc.nist.gov/CAVP/pqc. KAT files have ~100 vectors per parameter set. The FIPS 203 document (Section 8) also provides a short worked example. |
| sntrup761 | OpenSSH source `crypto_kem/sntrup761/ref/` has KAT generation code; reference outputs are in `KAT/kat_kem.rsp`. These are the authoritative vectors for the OpenSSH flavor. |
| X25519MLKEM768 (TLS) | No formal RFC-published vectors. Cross-check against Cloudflare CIRCL (`go-circl/kem/hybrid`) and Filippo Valsorda's `mlkem768` Go package, both of which implement the IETF draft combiner order. |
| sntrup761x25519 (SSH) | No formal RFC vectors. Cross-check against an OpenSSH 9.x server; capture the handshake with `-v` and verify K against a local computation. |

---

## 12. References

- FIPS 203 (2024-08-13): Module-Lattice-Based Key-Encapsulation Mechanism Standard (ML-KEM).
  https://doi.org/10.6028/NIST.FIPS.203
- FIPS 204 (2024-08-13): Module-Lattice-Based Digital Signature Standard (ML-DSA).
  https://doi.org/10.6028/NIST.FIPS.204
- FIPS 205 (2024-08-13): Stateless Hash-Based Digital Signature Standard (SLH-DSA).
  https://doi.org/10.6028/NIST.FIPS.205
- draft-ietf-tls-hybrid-design: Hybrid key exchange in TLS 1.3.
  https://datatracker.ietf.org/doc/draft-ietf-tls-hybrid-design/
- OpenSSH PROTOCOL file, section `sntrup761x25519-sha512@openssh.com`.
  https://github.com/openssh/openssh-portable/blob/master/PROTOCOL
- IRTF CFRG draft-irtf-cfrg-hybrid-kems: Hybrid KEMs for IETF protocols (combiners).
  https://datatracker.ietf.org/doc/draft-irtf-cfrg-hybrid-kems/
- Cloudflare blog: "The state of the post-quantum Internet" (2024).
  https://blog.cloudflare.com/post-quantum-cryptography-key-encapsulation-mechanisms/
- NTRU Prime specification: Bernstein et al., "NTRU Prime: reducing attack surface at low cost".
  https://ntruprime.cr.yp.to/

---

## 13. Cross-References

- `src/os/crypto/curve25519.spl` — X25519 classical half (shipped; the starting point for both
  hybrids)
- `src/os/crypto/sha512.spl` — SHA-512 (used by the SSH combiner)
- `src/os/tls13/hkdf.spl` — HKDF (used by the TLS 1.3 key schedule after combining)
- `src/os/tls13/handshake13.spl` — TLS 1.3 ClientHello/ServerHello; key_share extension
- `src/os/apps/sshd/ssh_kex.spl` — SSH KEX dispatcher; `_push_server_kex_algorithms`,
  `ssh_kex_compute_shared`
- `doc/04_architecture/ssh_algorithm_catalog.md` — SSH algorithm catalog; PQC entry belongs here
- `doc/04_architecture/simd_int_intrinsics_design.md` — SIMD design (NTT and polynomial
  arithmetic in ML-KEM will benefit from SIMD vectorization once that doc's proposals land)
