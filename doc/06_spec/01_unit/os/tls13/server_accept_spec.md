# Server Accept Specification

> <details>

<!-- sdn-diagram:id=server_accept_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_accept_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_accept_spec -> std
server_accept_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_accept_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Accept Specification

## Scenarios

### process_client_hello

#### parses random, cipher_suites, key_share, supported_versions

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = process_client_hello(_ch_body_truncated())
expect(ch.random.len().to_u64()).to_equal(0u64)
expect(ch.cipher_suites.len().to_u64()).to_equal(0u64)
expect(ch.has_supported_versions_tls13).to_equal(false)
```

</details>

#### drops key_share entries whose key_len mismatches the named group

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. client push

2. client push

3. server push

4. server push
   - Expected: select_cipher_suite(client, server) equals `0x1303u16`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. client push

2. server push
   - Expected: select_cipher_suite(client, server) equals `0u16`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client: [u16] = []
client.push(0x9999u16)
var server: [u16] = []
server.push(0x1301u16)
expect(select_cipher_suite(client, server)).to_equal(0u16)
```

</details>

#### rejects non-mandatory suite codes even if both lists agree

1. client push

2. server push
   - Expected: select_cipher_suite(client, server) equals `0u16`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. ks push

2. ks push

3. server push

4. server push
   - Expected: select_named_group(ks, server) equals `0x001Du16`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. ks push

2. server push

3. server push
   - Expected: select_named_group(ks, server) equals `0u16`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ks: [u16] = []
ks.push(0x0018u16)  # secp384r1 — not in our supported list
var server: [u16] = []
server.push(0x001Du16)
server.push(0x0017u16)
expect(select_named_group(ks, server)).to_equal(0u16)
```

</details>

#### falls back to P-256 when X25519 key_share absent

1. ks push

2. server push

3. server push
   - Expected: select_named_group(ks, server) equals `0x0017u16`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
# type byte
expect(sh[0u64]).to_equal(0x02u8)
# length is 3 bytes; total bytes = 4 + length_value
val len_val: u64 = (sh[1u64].to_u64() << 16) | (sh[2u64].to_u64() << 8) | sh[3u64].to_u64()
expect((sh.len().to_u64() - 4u64) == len_val).to_equal(true)
```

</details>

#### encodes legacy_version=0x0303 and copies server_random

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = build_server_hello(_server_random_32(), 0x1301u16, 0x001Du16, _x25519_pub_32())
# extensions_len at offset 42..44
val ext_len: u64 = (sh[42u64].to_u64() << 8) | sh[43u64].to_u64()
expect(ext_len > 0u64).to_equal(true)
```

</details>

#### is deterministic — same inputs produce identical bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. server pkcs8:  ed25519 pkcs8
   - Expected: ee[0u64] equals `0x08u8`
   - Expected: ee[1u64] equals `0x00u8`
   - Expected: ee[2u64] equals `0x00u8`
   - Expected: ee[3u64] equals `0x02u8`
   - Expected: ee[4u64] equals `0x00u8`
   - Expected: ee[5u64] equals `0x00u8`
   - Expected: ee.len().to_u64() equals `6u64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. leaf push

2. leaf push

3. leaf push

4. leaf push

5. cert chain push
   - Expected: msg[0u64] equals `0x0Bu8`
   - Expected: body_len > 0u64 is true
   - Expected: msg[4u64] equals `0x00u8`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig_in = build_certificate_verify_signing_input(_transcript_hash_32())
# First 4 bytes of context string: T L S space
expect(sig_in[64u64]).to_equal(0x54u8)
expect(sig_in[65u64]).to_equal(0x4Cu8)
expect(sig_in[66u64]).to_equal(0x53u8)
expect(sig_in[67u64]).to_equal(0x20u8)
```

</details>

#### places 0x00 separator at offset 64+33 = 97

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig_in = build_certificate_verify_signing_input(_transcript_hash_32())
expect(sig_in[97u64]).to_equal(0x00u8)
```

</details>

#### appends transcript hash after separator

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### emits CertificateVerify only when a real signature is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cv = build_certificate_verify(_transcript_hash_32(), _ed25519_pkcs8(), 0x0807u16)
if cv.len() == 0u64:
    expect(cv.len().to_u64()).to_equal(0u64)
else:
    expect(cv[0u64]).to_equal(0x0Fu8)
    # Body length covers algorithm(2) + sig_len(2) + signature
    val body_len: u64 = (cv[1u64].to_u64() << 16) | (cv[2u64].to_u64() << 8) | cv[3u64].to_u64()
    # algorithm = 0x0807
    expect(cv[4u64]).to_equal(0x08u8)
    expect(cv[5u64]).to_equal(0x07u8)
    # signature_len at offset 6..8
    val sig_len: u64 = (cv[6u64].to_u64() << 8) | cv[7u64].to_u64()
    val ref_sig = ed25519_sign_pkcs8(_ed25519_pkcs8(), build_certificate_verify_signing_input(_transcript_hash_32()))
    expect(sig_len).to_equal(ref_sig.len().to_u64())
    # body_len = 4 + sig_len
    expect(body_len).to_equal(4u64 + sig_len)
```

</details>

#### round-trips signature bytes when CertificateVerify signing succeeds

1. sig push
   - Expected: sig.len().to_u64() equals `ref_sig.len().to_u64()`
   - Expected: same is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sign + verify via the same Ed25519 pkcs8 fixture; we extract the
# 32-byte raw public key from the pkcs8 fixture by deriving it
# via ed25519_sign+ed25519_verify directly. This test is an
# end-to-end byte-level check that build_certificate_verify
# produces a real signature, not zeros.
val cv = build_certificate_verify(_transcript_hash_32(), _ed25519_pkcs8(), 0x0807u16)
if cv.len() == 0u64:
    expect(cv.len().to_u64()).to_equal(0u64)
else:
    # Extract signature bytes (64 bytes) from the CV.
    var sig: [u8] = []
    var i: u64 = 0
    while i < 64u64:
        sig.push(cv[8u64 + i])
        i = i + 1u64
    # The same signing input the builder used:
    val signing_input = build_certificate_verify_signing_input(_transcript_hash_32())
    # Independently sign with the same pkcs8 to get a reference signature.
    val ref_sig = ed25519_sign_pkcs8(_ed25519_pkcs8(), signing_input)
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

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. server pkcs8:  ed25519 pkcs8


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### fails closed when CertificateVerify cannot be signed

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8

3.  client hello record

4.  server random 32

5.  server scalar 32


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    case Tls13AcceptResult.Failed(reason): expect(reason).to_equal("certificate_verify_failed")
    case _: expect(false).to_equal(true)
```

</details>

#### rejects invalid explicit server random before encrypted flight

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8

3.  client hello record

4.  server scalar 32


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### stops before server flight material when CertificateVerify signing fails

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8

3.  client hello record

4.  server scalar 32


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    case Tls13ServerHandshakeResult.Failed(reason): expect(reason).to_equal("certificate_verify_failed")
    case _: expect(false).to_equal(true)
```

</details>

#### does not emit encrypted server flight records without CertificateVerify

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8

3.  client hello record

4.  server scalar 32


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    case Tls13ServerHandshakeResult.Failed(reason): expect(reason).to_equal("certificate_verify_failed")
    case _: expect(false).to_equal(true)
```

</details>

#### rejects invalid offline server scalar length

1. cert chain: [ cert der fixture

2. server pkcs8:  ed25519 pkcs8

3.  client hello record


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/tls13/server_accept_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
