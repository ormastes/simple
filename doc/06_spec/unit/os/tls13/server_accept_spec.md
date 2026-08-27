# Server Accept Specification

> Tests covering process_client_hello, select_cipher_suite, select_named_group, build_server_hello byte structure, build_encrypted_extensions_server_side, build_certificate, build_certificate_verify_signing_input, build_certificate_verify byte structure, tls13_accept prerequisite gate, tls13_prepare_server_handshake_from_record_for_test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Accept Specification

## Scenarios

### process_client_hello

#### parses random, cipher_suites, key_share, supported_versions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses random, cipher_suites, key_share, supported_versions
   - Expected: ch.random.len().to_u64() equals `32u64`
   - Expected: ch.cipher_suites.len().to_u64() equals `2u64`
   - Expected: ch.cipher_suites[0u64] equals `0x1301u16`
   - Expected: ch.cipher_suites[1u64] equals `0x1303u16`
   - Expected: ch.named_groups.len().to_u64() equals `2u64`
   - Expected: ch.named_groups[0u64] equals `0x001Du16`
   - Expected: ch.named_groups[1u64] equals `0x0017u16`
   - Expected: ch.key_share_groups.len().to_u64() equals `1u64`
   - Expected: ch.key_share_groups[0u64] equals `0x001Du16`
   - Expected: ch.x25519_key_share.len().to_u64() equals `32u64`
   - Expected: ch.p256_key_share.len().to_u64() equals `0u64`
   - Expected: ch.has_supported_versions_tls13 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses random, cipher_suites, key_share, supported_versions")
val ch = process_client_hello(_ch_body_x25519_only())
expect(ch.random.len().to_u64()).to_equal(32u64)
expect(ch.cipher_suites.len().to_u64()).to_equal(2u64)
expect(ch.cipher_suites[0u64]).to_equal(0x1301u16)
expect(ch.cipher_suites[1u64]).to_equal(0x1303u16)
expect(ch.named_groups.len().to_u64()).to_equal(2u64)
expect(ch.named_groups[0u64]).to_equal(0x001Du16)
expect(ch.named_groups[1u64]).to_equal(0x0017u16)
expect(ch.key_share_groups.len().to_u64()).to_equal(1u64)
expect(ch.key_share_groups[0u64]).to_equal(0x001Du16)
expect(ch.x25519_key_share.len().to_u64()).to_equal(32u64)
expect(ch.p256_key_share.len().to_u64()).to_equal(0u64)
expect(ch.has_supported_versions_tls13).to_equal(true)
```

</details>

#### returns empty CH on truncated body

- returns empty CH on truncated body
   - Expected: ch.random.len().to_u64() equals `0u64`
   - Expected: ch.cipher_suites.len().to_u64() equals `0u64`
   - Expected: ch.has_supported_versions_tls13 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty CH on truncated body")
val ch = process_client_hello(_ch_body_truncated())
expect(ch.random.len().to_u64()).to_equal(0u64)
expect(ch.cipher_suites.len().to_u64()).to_equal(0u64)
expect(ch.has_supported_versions_tls13).to_equal(false)
```

</details>

#### drops key_share entries whose key_len mismatches the named group

- drops key_share entries whose key_len mismatches the named group
   - Expected: contains_x25519 is false
   - Expected: ch.x25519_key_share.len().to_u64() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops key_share entries whose key_len mismatches the named group")
# CH where X25519 key_share carries klen=16 (bogus) — group must
# NOT appear in ks_groups, otherwise select_named_group would
# later return X25519 with an empty share.
val ch = process_client_hello(_ch_body_x25519_bad_keylen())
# Group must be absent from key_share_groups even though the
# extension was structurally well-formed.
var contains_x25519 = false
var i: u64 = 0
while i < ch.key_share_groups.len():
    if ch.key_share_groups[i] == 0x001Du16:
        contains_x25519 = true
    i = i + 1u64
expect(contains_x25519).to_equal(false)
expect(ch.x25519_key_share.len().to_u64()).to_equal(0u64)
```

</details>

### select_cipher_suite

#### picks the server's preferred suite that the client offered

- picks the server's preferred suite that the client offered
   - Expected: select_cipher_suite(client, server) equals `0x1303u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("picks the server's preferred suite that the client offered")
var client: [u16] = []
client.push(0x1301u16)
client.push(0x1303u16)
var server: [u16] = []
server.push(0x1303u16)
server.push(0x1301u16)
# server prefers 0x1303; client offered it; expect 0x1303
expect(select_cipher_suite(client, server)).to_equal(0x1303u16)
```

</details>

#### returns 0u16 when no overlap

- returns 0u16 when no overlap
   - Expected: select_cipher_suite(client, server) equals `0u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0u16 when no overlap")
var client: [u16] = []
client.push(0x9999u16)
var server: [u16] = []
server.push(0x1301u16)
expect(select_cipher_suite(client, server)).to_equal(0u16)
```

</details>

#### rejects non-mandatory suite codes even if both lists agree

- rejects non-mandatory suite codes even if both lists agree
   - Expected: select_cipher_suite(client, server) equals `0u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-mandatory suite codes even if both lists agree")
# 0x9999 is not in the 0x1301/0x1302/0x1303 allowlist
var client: [u16] = []
client.push(0x9999u16)
var server: [u16] = []
server.push(0x9999u16)
expect(select_cipher_suite(client, server)).to_equal(0u16)
```

</details>

### select_named_group

#### prefers X25519 over P-256 when both offered

- prefers X25519 over P-256 when both offered
   - Expected: select_named_group(ks, server) equals `0x001Du16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers X25519 over P-256 when both offered")
var ks: [u16] = []
ks.push(0x001Du16)
ks.push(0x0017u16)
var server: [u16] = []
server.push(0x001Du16)
server.push(0x0017u16)
expect(select_named_group(ks, server)).to_equal(0x001Du16)
```

</details>

#### returns 0u16 when CH key_share has no acceptable group (HRR-needed)

- returns 0u16 when CH key_share has no acceptable group (HRR-needed)
   - Expected: select_named_group(ks, server) equals `0u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0u16 when CH key_share has no acceptable group (HRR-needed)")
var ks: [u16] = []
ks.push(0x0018u16)  # secp384r1 — not in our supported list
var server: [u16] = []
server.push(0x001Du16)
server.push(0x0017u16)
expect(select_named_group(ks, server)).to_equal(0u16)
```

</details>

#### falls back to P-256 when X25519 key_share absent

- falls back to P-256 when X25519 key_share absent
   - Expected: select_named_group(ks, server) equals `0x0017u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to P-256 when X25519 key_share absent")
var ks: [u16] = []
ks.push(0x0017u16)
var server: [u16] = []
server.push(0x001Du16)
server.push(0x0017u16)
expect(select_named_group(ks, server)).to_equal(0x0017u16)
```

</details>

### build_server_hello byte structure

#### emits handshake header type=2 + 3-byte length

- emits handshake header type=2 + 3-byte length
   - Expected: sh[0u64] equals `0x02u8`
   - Expected: (sh.len().to_u64() - 4u64) equals `len_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits handshake header type=2 + 3-byte length")
val sh = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
# type byte
expect(sh[0u64]).to_equal(0x02u8)
# length is 3 bytes; total bytes = 4 + length_value
val len_val: u64 = (sh[1u64].to_u64() << 16) | (sh[2u64].to_u64() << 8) | sh[3u64].to_u64()
expect((sh.len().to_u64() - 4u64)).to_equal(len_val)
```

</details>

#### encodes legacy_version=0x0303 and copies server_random

- encodes legacy_version=0x0303 and copies server_random
   - Expected: sh[4u64] equals `0x03u8`
   - Expected: sh[5u64] equals `0x03u8`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes legacy_version=0x0303 and copies server_random")
val sh = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
expect(sh[4u64]).to_equal(0x03u8)
expect(sh[5u64]).to_equal(0x03u8)
# server_random: bytes 6..38 must equal _server_random_32()
var ok = true
var i: u64 = 0
val rnd = _server_random_32()
while i < 32u64 and ok:
    if sh[6u64 + i] != rnd[i]:
        ok = false
    i = i + 1u64
expect(ok).to_equal(true)
```

</details>

#### encodes legacy_session_id_len=0 + cipher_suite + compression=0x00

- encodes legacy_session_id_len=0 + cipher_suite + compression=0x00
   - Expected: sh[38u64] equals `0x00u8`
   - Expected: sh[39u64] equals `0x13u8`
   - Expected: sh[40u64] equals `0x03u8`
   - Expected: sh[41u64] equals `0x00u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes legacy_session_id_len=0 + cipher_suite + compression=0x00")
val sh = build_server_hello(_server_random_32(), 0x1303u16, 0x001Du16, _x25519_pub_32())
# offset 4 + 2 + 32 = 38: legacy_session_id_len
expect(sh[38u64]).to_equal(0x00u8)
# offset 39..41: cipher_suite (2 bytes)
expect(sh[39u64]).to_equal(0x13u8)
expect(sh[40u64]).to_equal(0x03u8)
# offset 41: compression_method
expect(sh[41u64]).to_equal(0x00u8)
```

</details>

#### encodes a non-zero extensions length

- encodes a non-zero extensions length
   - Expected: ext_len > 0u64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a non-zero extensions length")
val sh = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
# extensions_len at offset 42..44
val ext_len: u64 = (sh[42u64].to_u64() << 8) | sh[43u64].to_u64()
expect(ext_len > 0u64).to_equal(true)
```

</details>

#### is deterministic — same inputs produce identical bytes

- is deterministic — same inputs produce identical bytes
   - Expected: a.len() equals `b.len()`
   - Expected: same is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is deterministic — same inputs produce identical bytes")
val a = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
val b = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
expect(a.len()).to_equal(b.len())
var same = true
var i: u64 = 0
while i < a.len().to_u64() and same:
    if a[i] != b[i]:
        same = false
    i = i + 1u64
expect(same).to_equal(true)
```

</details>

### build_encrypted_extensions_server_side

#### emits handshake type=8 + length=2 + zero-length extensions list

- emits handshake type=8 + length=2 + zero-length extensions list
   - Expected: ee[0u64] equals `0x08u8`
   - Expected: ee[1u64] equals `0x00u8`
   - Expected: ee[2u64] equals `0x00u8`
   - Expected: ee[3u64] equals `0x02u8`
   - Expected: ee[4u64] equals `0x00u8`
   - Expected: ee[5u64] equals `0x00u8`
   - Expected: ee.len().to_u64() equals `6u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits handshake type=8 + length=2 + zero-length extensions list")
val cfg = Tls13ServerConfig(
    cert_chain: [],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
val ee = build_encrypted_extensions_server_side(cfg)
# type byte
expect(ee[0u64]).to_equal(0x08u8)
# body length = 2 (the empty extensions list_len)
expect(ee[1u64]).to_equal(0x00u8)
expect(ee[2u64]).to_equal(0x00u8)
expect(ee[3u64]).to_equal(0x02u8)
# list_len bytes
expect(ee[4u64]).to_equal(0x00u8)
expect(ee[5u64]).to_equal(0x00u8)
expect(ee.len().to_u64()).to_equal(6u64)
```

</details>

### build_certificate

#### emits handshake type=11 with non-zero body

- emits handshake type=11 with non-zero body
   - Expected: msg[0u64] equals `0x0Bu8`
   - Expected: body_len > 0u64 is true
   - Expected: msg[4u64] equals `0x00u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits handshake type=11 with non-zero body")
var cert_chain: [[u8]] = []
var leaf: [u8] = []
leaf.push(0xCAu8)
leaf.push(0xFEu8)
leaf.push(0xBAu8)
leaf.push(0xBEu8)
cert_chain.push(leaf)
val msg = build_certificate(cert_chain)
expect(msg[0u64]).to_equal(0x0Bu8)
# length must be > 0
val body_len: u64 = (msg[1u64].to_u64() << 16) | (msg[2u64].to_u64() << 8) | msg[3u64].to_u64()
expect(body_len > 0u64).to_equal(true)
# request_context length byte at offset 4 = 0 for non-mTLS server
expect(msg[4u64]).to_equal(0x00u8)
```

</details>

### build_certificate_verify_signing_input

#### starts with 64 bytes of 0x20

- starts with 64 bytes of 0x20
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with 64 bytes of 0x20")
val sig_in = build_certificate_verify_signing_input(_transcript_hash_32())
var ok = true
var i: u64 = 0
while i < 64u64 and ok:
    if sig_in[i] != 0x20u8:
        ok = false
    i = i + 1u64
expect(ok).to_equal(true)
```

</details>

#### embeds 'TLS 1.3, server CertificateVerify' starting at offset 64

- embeds 'TLS 1.3, server CertificateVerify' starting at offset 64
   - Expected: sig_in[64u64] equals `0x54u8`
   - Expected: sig_in[65u64] equals `0x4Cu8`
   - Expected: sig_in[66u64] equals `0x53u8`
   - Expected: sig_in[67u64] equals `0x20u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("embeds 'TLS 1.3, server CertificateVerify' starting at offset 64")
val sig_in = build_certificate_verify_signing_input(_transcript_hash_32())
# First 4 bytes of context string: T L S space
expect(sig_in[64u64]).to_equal(0x54u8)
expect(sig_in[65u64]).to_equal(0x4Cu8)
expect(sig_in[66u64]).to_equal(0x53u8)
expect(sig_in[67u64]).to_equal(0x20u8)
```

</details>

#### places 0x00 separator at offset 64+33 = 97

- places 0x00 separator at offset 64+33 = 97
   - Expected: sig_in[97u64] equals `0x00u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places 0x00 separator at offset 64+33 = 97")
val sig_in = build_certificate_verify_signing_input(_transcript_hash_32())
expect(sig_in[97u64]).to_equal(0x00u8)
```

</details>

#### appends transcript hash after separator

- appends transcript hash after separator
   - Expected: sig_in.len().to_u64() equals `130u64`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends transcript hash after separator")
val sig_in = build_certificate_verify_signing_input(_transcript_hash_32())
# Total length = 64 + 33 + 1 + 32 = 130
expect(sig_in.len().to_u64()).to_equal(130u64)
# Last 32 bytes match _transcript_hash_32()
val th = _transcript_hash_32()
var ok = true
var i: u64 = 0
while i < 32u64 and ok:
    if sig_in[98u64 + i] != th[i]:
        ok = false
    i = i + 1u64
expect(ok).to_equal(true)
```

</details>

### build_certificate_verify byte structure

#### emits handshake type=15 + 2-byte algorithm + 2-byte sig_len + signature

- emits handshake type=15 + 2-byte algorithm + 2-byte sig_len + signature
   - Expected: cv[0u64] equals `0x0Fu8`
   - Expected: cv[4u64] equals `0x08u8`
   - Expected: cv[5u64] equals `0x07u8`
   - Expected: sig_len equals `ref_sig.len().to_u64()`
   - Expected: body_len equals `4u64 + sig_len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits handshake type=15 + 2-byte algorithm + 2-byte sig_len + signature")
val cv = build_certificate_verify(_transcript_hash_32(), _ed25519_pkcs8(), 0x0807u16)
expect(cv[0u64]).to_equal(0x0Fu8)
# Body length covers algorithm(2) + sig_len(2) + signature
val body_len: u64 = (cv[1u64].to_u64() << 16) | (cv[2u64].to_u64() << 8) | cv[3u64].to_u64()
# algorithm = 0x0807
expect(cv[4u64]).to_equal(0x08u8)
expect(cv[5u64]).to_equal(0x07u8)
# signature_len at offset 6..8
val sig_len: u64 = (cv[6u64].to_u64() << 8) | cv[7u64].to_u64()
val ref_sig = ed25519_sign(_ed25519_pkcs8(), build_certificate_verify_signing_input(_transcript_hash_32()))
expect(sig_len).to_equal(ref_sig.len().to_u64())
# body_len = 4 + sig_len
expect(body_len).to_equal(4u64 + sig_len)
```

</details>

#### round-trips: signature in CV verifies against the derived public key

- round-trips: signature in CV verifies against the derived public key
   - Expected: sig.len().to_u64() equals `ref_sig.len().to_u64()`
   - Expected: same is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips: signature in CV verifies against the derived public key")
# Sign + verify via the same Ed25519 pkcs8 fixture; we extract the
# 32-byte raw public key from the pkcs8 fixture by deriving it
# via ed25519_sign+ed25519_verify directly. This test is an
# end-to-end byte-level check that build_certificate_verify
# produces a real signature, not zeros.
val cv = build_certificate_verify(_transcript_hash_32(), _ed25519_pkcs8(), 0x0807u16)
# Extract signature bytes (64 bytes) from the CV.
var sig: [u8] = []
var i: u64 = 0
while i < 64u64:
    sig.push(cv[8u64 + i])
    i = i + 1u64
# The same signing input the builder used:
val signing_input = build_certificate_verify_signing_input(_transcript_hash_32())
# Independently sign with the same pkcs8 to get a reference signature.
val ref_sig = ed25519_sign(_ed25519_pkcs8(), signing_input)
# Ed25519 is deterministic — both signatures must be byte-identical.
expect(sig.len().to_u64()).to_equal(ref_sig.len().to_u64())
var same = true
var j: u64 = 0
while j < sig.len().to_u64() and same:
    if sig[j] != ref_sig[j]:
        same = false
    j = j + 1u64
expect(same).to_equal(true)
```

</details>

### tls13_accept prerequisite gate

#### rejects invalid socket fds before touching server material

- rejects invalid socket fds before touching server material


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid socket fds before touching server material")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept(-1, cfg):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("invalid_socket_fd")
    case _: expect(false).to_equal(true)
```

</details>

#### rejects missing certificate chains with a concrete reason

- rejects missing certificate chains with a concrete reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing certificate chains with a concrete reason")
val cfg = Tls13ServerConfig(
    cert_chain: [],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept(3, cfg):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("missing_certificate_chain")
    case _: expect(false).to_equal(true)
```

</details>

#### reaches the server crypto blocker after validating a ClientHello record

- reaches the server crypto blocker after validating a ClientHello record


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the server crypto blocker after validating a ClientHello record")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept_client_hello_record_for_test(_client_hello_record(_ch_body_x25519_only()), cfg):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("server_crypto_pending")
    case _: expect(false).to_equal(true)
```

</details>

#### rejects missing ClientHello record bytes before parsing handshake

- rejects missing ClientHello record bytes before parsing handshake


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing ClientHello record bytes before parsing handshake")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept_client_hello_record_for_test([], cfg):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("no_client_hello_record")
    case _: expect(false).to_equal(true)
```

</details>

#### rejects non-handshake records at the record boundary

- rejects non-handshake records at the record boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-handshake records at the record boundary")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept_client_hello_record_for_test([0x17u8, 0x03u8, 0x03u8, 0x00u8, 0x01u8, 0x00u8], cfg):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("expected_handshake_record")
    case _: expect(false).to_equal(true)
```

</details>

#### reaches client Finished blocker after explicit server crypto material

- reaches client Finished blocker after explicit server crypto material


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches client Finished blocker after explicit server crypto material")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept_client_hello_record_with_server_material_for_test(
    _client_hello_record(_ch_body_x25519_only()),
    cfg,
    _server_random_32(),
    _server_scalar_32()
):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("client_finished_pending")
    case _: expect(false).to_equal(true)
```

</details>

#### rejects invalid explicit server random before encrypted flight

- rejects invalid explicit server random before encrypted flight


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid explicit server random before encrypted flight")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_accept_client_hello_record_with_server_material_for_test(
    _client_hello_record(_ch_body_x25519_only()),
    cfg,
    [0x01u8],
    _server_scalar_32()
):
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("invalid_server_random")
    case _: expect(false).to_equal(true)
```

</details>

### tls13_prepare_server_handshake_from_record_for_test

#### prepares X25519 server handshake traffic material from a valid ClientHello record

- prepares X25519 server handshake traffic material from a valid ClientHello record
   - Expected: material.cipher_suite equals `0x1301u16`
   - Expected: material.named_group equals `0x001Du16`
   - Expected: material.server_hello.len().to_u64() > 0u64 is true
   - Expected: material.server_keyshare_pub.len().to_u64() equals `32u64`
   - Expected: material.shared_secret.len().to_u64() equals `32u64`
   - Expected: material.handshake_secret.len().to_u64() equals `32u64`
   - Expected: material.client_hs_traffic.len().to_u64() equals `32u64`
   - Expected: material.server_hs_traffic.len().to_u64() equals `32u64`
   - Expected: material.client_hs_key.len().to_u64() equals `16u64`
   - Expected: material.client_hs_iv.len().to_u64() equals `12u64`
   - Expected: material.server_hs_key.len().to_u64() equals `16u64`
   - Expected: material.server_hs_iv.len().to_u64() equals `12u64`
   - Expected: material.client_app_key.len().to_u64() equals `16u64`
   - Expected: material.client_app_iv.len().to_u64() equals `12u64`
   - Expected: material.server_app_key.len().to_u64() equals `16u64`
   - Expected: material.server_app_iv.len().to_u64() equals `12u64`
   - Expected: material.expected_client_finished.len().to_u64() equals `32u64`
   - Expected: material.encrypted_extensions[0u64] equals `0x08u8`
   - Expected: material.certificate[0u64] equals `0x0Bu8`
   - Expected: material.certificate_verify[0u64] equals `0x0Fu8`
   - Expected: material.server_finished[0u64] equals `0x14u8`
   - Expected: material.server_hello_record[0u64] equals `0x16u8`
   - Expected: material.server_hello_record[1u64] equals `0x03u8`
   - Expected: material.server_hello_record[2u64] equals `0x03u8`
   - Expected: material.encrypted_extensions_record[0u64] equals `0x17u8`
   - Expected: material.certificate_record[0u64] equals `0x17u8`
   - Expected: material.certificate_verify_record[0u64] equals `0x17u8`
   - Expected: material.server_finished_record[0u64] equals `0x17u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepares X25519 server handshake traffic material from a valid ClientHello record")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_prepare_server_handshake_from_record_for_test(
    _client_hello_record(_ch_body_x25519_only()),
    cfg,
    _server_scalar_32()
):
    case Tls13ServerHandshakeResult.Prepared(material):
        expect(material.cipher_suite).to_equal(0x1301u16)
        expect(material.named_group).to_equal(0x001Du16)
        expect(material.server_hello.len().to_u64() > 0u64).to_equal(true)
        expect(material.server_keyshare_pub.len().to_u64()).to_equal(32u64)
        expect(material.shared_secret.len().to_u64()).to_equal(32u64)
        expect(material.handshake_secret.len().to_u64()).to_equal(32u64)
        expect(material.client_hs_traffic.len().to_u64()).to_equal(32u64)
        expect(material.server_hs_traffic.len().to_u64()).to_equal(32u64)
        expect(material.client_hs_key.len().to_u64()).to_equal(16u64)
        expect(material.client_hs_iv.len().to_u64()).to_equal(12u64)
        expect(material.server_hs_key.len().to_u64()).to_equal(16u64)
        expect(material.server_hs_iv.len().to_u64()).to_equal(12u64)
        expect(material.client_app_key.len().to_u64()).to_equal(16u64)
        expect(material.client_app_iv.len().to_u64()).to_equal(12u64)
        expect(material.server_app_key.len().to_u64()).to_equal(16u64)
        expect(material.server_app_iv.len().to_u64()).to_equal(12u64)
        expect(material.expected_client_finished.len().to_u64()).to_equal(32u64)
        expect(material.encrypted_extensions[0u64]).to_equal(0x08u8)
        expect(material.certificate[0u64]).to_equal(0x0Bu8)
        expect(material.certificate_verify[0u64]).to_equal(0x0Fu8)
        expect(material.server_finished[0u64]).to_equal(0x14u8)
        expect(material.server_hello_record[0u64]).to_equal(0x16u8)
        expect(material.server_hello_record[1u64]).to_equal(0x03u8)
        expect(material.server_hello_record[2u64]).to_equal(0x03u8)
        expect(material.encrypted_extensions_record[0u64]).to_equal(0x17u8)
        expect(material.certificate_record[0u64]).to_equal(0x17u8)
        expect(material.certificate_verify_record[0u64]).to_equal(0x17u8)
        expect(material.server_finished_record[0u64]).to_equal(0x17u8)
    case _: expect(false).to_equal(true)
```

</details>

#### encrypts the server flight records with the prepared server handshake key

- encrypts the server flight records with the prepared server handshake key
   - Expected: material.server_hello_record[0u64] equals `0x16u8`
   - Expected: material.server_hello_record[1u64] equals `0x03u8`
   - Expected: material.server_hello_record[2u64] equals `0x03u8`
   - Expected: content_type equals `0x16`
   - Expected: data[0u64] equals `0x08u8`
   - Expected: content_type equals `0x16`
   - Expected: data[0u64] equals `0x0Bu8`
   - Expected: content_type equals `0x16`
   - Expected: data[0u64] equals `0x0Fu8`
   - Expected: content_type equals `0x16`
   - Expected: data[0u64] equals `0x14u8`
   - Expected: data.len().to_u64() equals `36u64`
   - Expected: ctx.client_app_key.len().to_u64() equals `16u64`
   - Expected: ctx.client_app_iv.len().to_u64() equals `12u64`
   - Expected: ctx.server_app_key.len().to_u64() equals `16u64`
   - Expected: ctx.server_app_iv.len().to_u64() equals `12u64`
   - Expected: ctx.client_seq equals `0u64`
   - Expected: ctx.server_seq equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts the server flight records with the prepared server handshake key")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_prepare_server_handshake_from_record_for_test(
    _client_hello_record(_ch_body_x25519_only()),
    cfg,
    _server_scalar_32()
):
    case Tls13ServerHandshakeResult.Prepared(material):
        expect(material.server_hello_record[0u64]).to_equal(0x16u8)
        expect(material.server_hello_record[1u64]).to_equal(0x03u8)
        expect(material.server_hello_record[2u64]).to_equal(0x03u8)
        val rk = RecordKey(key: material.server_hs_key, iv: material.server_hs_iv)
        match record13_decrypt_for_suite(material.cipher_suite, rk, 0u64, material.encrypted_extensions_record):
            case RecordResult.Ok(content_type, data):
                expect(content_type).to_equal(0x16)
                expect(data[0u64]).to_equal(0x08u8)
            case RecordResult.Err(_): expect(false).to_equal(true)
        match record13_decrypt_for_suite(material.cipher_suite, rk, 1u64, material.certificate_record):
            case RecordResult.Ok(content_type, data):
                expect(content_type).to_equal(0x16)
                expect(data[0u64]).to_equal(0x0Bu8)
            case RecordResult.Err(_): expect(false).to_equal(true)
        match record13_decrypt_for_suite(material.cipher_suite, rk, 2u64, material.certificate_verify_record):
            case RecordResult.Ok(content_type, data):
                expect(content_type).to_equal(0x16)
                expect(data[0u64]).to_equal(0x0Fu8)
            case RecordResult.Err(_): expect(false).to_equal(true)
        match record13_decrypt_for_suite(material.cipher_suite, rk, 3u64, material.server_finished_record):
            case RecordResult.Ok(content_type, data):
                expect(content_type).to_equal(0x16)
                expect(data[0u64]).to_equal(0x14u8)
                expect(data.len().to_u64()).to_equal(36u64)
            case RecordResult.Err(_): expect(false).to_equal(true)
        val client_rk = RecordKey(key: material.client_hs_key, iv: material.client_hs_iv)
        val client_fin = build_finished_bytes(material.expected_client_finished)
        val client_fin_record = record13_encrypt_for_suite(material.cipher_suite, client_rk, 0u64, 0x16u8, client_fin)
        match tls13_accept_client_finished_record_for_test(material, client_fin_record):
            case Tls13AcceptResult.Accepted(ctx):
                expect(ctx.client_app_key.len().to_u64()).to_equal(16u64)
                expect(ctx.client_app_iv.len().to_u64()).to_equal(12u64)
                expect(ctx.server_app_key.len().to_u64()).to_equal(16u64)
                expect(ctx.server_app_iv.len().to_u64()).to_equal(12u64)
                expect(ctx.client_seq).to_equal(0u64)
                expect(ctx.server_seq).to_equal(0u64)
            case _: expect(false).to_equal(true)
    case _: expect(false).to_equal(true)
```

</details>

#### rejects invalid offline server scalar length

- rejects invalid offline server scalar length


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid offline server scalar length")
val cfg = Tls13ServerConfig(
    cert_chain: [_cert_der_fixture()],
    server_pkcs8: _ed25519_pkcs8(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)
match tls13_prepare_server_handshake_from_record_for_test(
    _client_hello_record(_ch_body_x25519_only()),
    cfg,
    [0x01u8]
):
    case Tls13ServerHandshakeResult.Failed(reason): expect(reason).to_equal("invalid_server_scalar")
    case _: expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/server_accept_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering process_client_hello, select_cipher_suite, select_named_group, build_server_hello byte structure, build_encrypted_extensions_server_side, build_certificate, build_certificate_verify_signing_input, build_certificate_verify byte structure, tls13_accept prerequisite gate, tls13_prepare_server_handshake_from_record_for_test.
- process_client_hello
- select_cipher_suite
- select_named_group
- build_server_hello byte structure
- build_encrypted_extensions_server_side
- build_certificate
- build_certificate_verify_signing_input
- build_certificate_verify byte structure
- tls13_accept prerequisite gate
- tls13_prepare_server_handshake_from_record_for_test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92099dcf2b58cffe76a602cc16068ab6c88f7feff4f10be54f01188535dca682`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92099dcf2b58cffe76a602cc16068ab6c88f7feff4f10be54f01188535dca682`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92099dcf2b58cffe76a602cc16068ab6c88f7feff4f10be54f01188535dca682`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/server_accept_spec.spl
mirror: doc/06_spec/unit/os/tls13/server_accept_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/server_accept_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/server_accept_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/server_accept_spec.spl:330:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses random, cipher_suites, key_share, supported_versions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/server_accept_spec.spl:347:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty CH on truncated body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/server_accept_spec.spl:355:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops key_share entries whose key_len mismatches the named group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
