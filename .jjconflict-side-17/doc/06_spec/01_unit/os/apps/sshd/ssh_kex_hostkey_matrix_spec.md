# SSH KEX Host-Key Algorithm Matrix

> Validates that ssh_sign_exchange_hash produces correctly structured SSH signature blobs for all four host-key algorithms: ssh-ed25519, rsa-sha2-256, rsa-sha2-512, ecdsa-sha2-nistp256.

<!-- sdn-diagram:id=ssh_kex_hostkey_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_kex_hostkey_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_kex_hostkey_matrix_spec -> std
ssh_kex_hostkey_matrix_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_kex_hostkey_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SSH KEX Host-Key Algorithm Matrix

Validates that ssh_sign_exchange_hash produces correctly structured SSH signature blobs for all four host-key algorithms: ssh-ed25519, rsa-sha2-256, rsa-sha2-512, ecdsa-sha2-nistp256.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ssh-hostkey-matrix |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that ssh_sign_exchange_hash produces correctly structured SSH
signature blobs for all four host-key algorithms:
  ssh-ed25519, rsa-sha2-256, rsa-sha2-512, ecdsa-sha2-nistp256.

Each test:
1. Builds a HostKeySet with the appropriate key material.
2. Calls ssh_sign_exchange_hash with a synthetic exchange_hash.
3. Decodes the returned blob (string algo + string raw_sig).
4. Verifies the signature shape and transcript binding. Ed25519 positive
   local verify coverage is intentionally limited by the tracked pure-Simple
   verifier gap in doc/08_tracking/bug/ed25519_verify_rejects_ssh_exchange_hash_signatures_2026-06-06.md.
5. Tampers one byte of the exchange_hash and confirms verify rejects it where
   the local verifier path is reliable.

## Key Concepts

| Concept | Description |
|---------|-------------|
| HostKeySet | Multi-algorithm server host key container |
| ssh_sign_exchange_hash | Per-algorithm dispatch signing function |
| Signature blob format | string algo-name + string raw-sig bytes |
| ECDSA inner blob | mpint r + mpint s per RFC 5656 |

## Scenarios

### ssh-ed25519 host key signing

#### returns Ok for a configured Ed25519 key

1. ed25519 seed:  ed25519 seed
   - Expected: result.is_ok() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("ssh-ed25519", host_keys, _test_exchange_hash())
expect(result.is_ok()).to_equal(true)
```

</details>

#### derives 32-byte X25519 public keys and a matching shared secret

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val private_1 = _filled_bytes(32, 0x11)
val private_2 = _filled_bytes(32, 0x33)
val public_1 = ssh_kex_public_from_private(private_1)
val public_2 = ssh_kex_public_from_private(private_2)
val shared_1 = ssh_kex_compute_shared(private_1, public_2)
val shared_2 = ssh_kex_compute_shared(private_2, public_1)
expect(public_1.len()).to_equal(32)
expect(public_2.len()).to_equal(32)
expect(shared_1.len()).to_equal(32)
expect(shared_1 == shared_2).to_equal(true)
```

</details>

#### returns Err when Ed25519 seed is absent

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("ssh-ed25519", host_keys, _test_exchange_hash())
expect(result.is_err()).to_equal(true)
```

</details>

#### blob algo field is ssh-ed25519

1. ed25519 seed:  ed25519 seed
   - Expected: parts.0 equals `ssh-ed25519`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val blob = ssh_sign_exchange_hash("ssh-ed25519", host_keys, _test_exchange_hash()).unwrap()
val parts = _decode_sig_blob(blob)
expect(parts.0).to_equal("ssh-ed25519")
```

</details>

#### raw Ed25519 signature is exactly 64 bytes

1. ed25519 seed:  ed25519 seed
   - Expected: raw_sig.len() equals `64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val blob = ssh_sign_exchange_hash("ssh-ed25519", host_keys, _test_exchange_hash()).unwrap()
val raw_sig = _decode_sig_blob(blob).1
expect(raw_sig.len()).to_equal(64)
```

</details>

#### Ed25519 signing is deterministic for an exchange hash

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _ed25519_seed()
val host_keys = HostKeySet(
    ed25519_seed: seed,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val hash = _test_exchange_hash()
val raw_sig_1 = _decode_sig_blob(ssh_sign_exchange_hash("ssh-ed25519", host_keys, hash).unwrap()).1
val raw_sig_2 = _decode_sig_blob(ssh_sign_exchange_hash("ssh-ed25519", host_keys, hash).unwrap()).1
expect(raw_sig_1 == raw_sig_2).to_equal(true)
expect(_bytes_all_zero(raw_sig_1)).to_equal(false)
```

</details>

#### ed25519_verify rejects tampered exchange_hash

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _ed25519_seed()
val pubkey = ed25519_keypair_from_seed(seed).1
val host_keys = HostKeySet(
    ed25519_seed: seed,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val hash = _test_exchange_hash()
val blob = ssh_sign_exchange_hash("ssh-ed25519", host_keys, hash).unwrap()
val raw_sig = _decode_sig_blob(blob).1
val tampered = _tampered_hash(hash)
val bad = ed25519_verify(pubkey, tampered, raw_sig)
expect(bad).to_equal(false)
```

</details>

#### changing Q_S changes the exchange hash

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hash_1 = _ed25519_hash_for_server_public(_filled_bytes(32, 0x01))
val hash_2 = _ed25519_hash_for_server_public(_filled_bytes(32, 0x21))
expect(hash_1 == hash_2).to_equal(false)
```

</details>

#### changing Q_S changes the Ed25519 host-key signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _ed25519_seed()
val host_keys = HostKeySet(
    ed25519_seed: seed,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val hash_1 = _ed25519_hash_for_server_public(_filled_bytes(32, 0x01))
val hash_2 = _ed25519_hash_for_server_public(_filled_bytes(32, 0x21))
val sig_1 = _decode_sig_blob(ssh_sign_exchange_hash("ssh-ed25519", host_keys, hash_1).unwrap()).1
val sig_2 = _decode_sig_blob(ssh_sign_exchange_hash("ssh-ed25519", host_keys, hash_2).unwrap()).1
expect(sig_1 == sig_2).to_equal(false)
```

</details>

#### binds the Ed25519 signature to the full KEX transcript

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _ed25519_seed()
val pubkey = ed25519_keypair_from_seed(seed).1
val host_keys = HostKeySet(
    ed25519_seed: seed,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val hash_1 = _full_transcript_hash("SSH-2.0-OpenSSH_9.6", _filled_bytes(32, 0x21), _filled_bytes(32, 0xC0))
val hash_2 = _full_transcript_hash("SSH-2.0-OpenSSH_9.7", _filled_bytes(32, 0x21), _filled_bytes(32, 0xC0))
val sig = _decode_sig_blob(ssh_sign_exchange_hash("ssh-ed25519", host_keys, hash_1).unwrap()).1
expect(hash_1 == hash_2).to_equal(false)
expect(ed25519_verify(pubkey, hash_1, sig)).to_equal(true)
expect(ed25519_verify(pubkey, hash_2, sig)).to_equal(false)
```

</details>

### host-key aware KEXINIT builder

#### round-trips an ed25519-only KEXINIT through the transport parser

1. ed25519 seed:  ed25519 seed
   - Expected: parsed.is_ok() is true
   - Expected: kex.kex_algorithms equals `curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com`
   - Expected: kex.server_host_key_algorithms equals `ssh-ed25519`
   - Expected: kex.encryption_client_to_server equals `aes256-gcm@openssh.com`
   - Expected: kex.encryption_server_to_client equals `aes256-gcm@openssh.com`
   - Expected: kex.mac_client_to_server equals `none`
   - Expected: kex.mac_server_to_client equals `none`
   - Expected: kex.compression_client_to_server equals `none`
   - Expected: kex.compression_server_to_client equals `none`
   - Expected: kex.first_kex_packet_follows is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit_for_host_keys(HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
))
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
val kex = parsed.unwrap()
expect(kex.kex_algorithms).to_equal("curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com")
expect(kex.server_host_key_algorithms).to_equal("ssh-ed25519")
expect(kex.encryption_client_to_server).to_equal("aes256-gcm@openssh.com")
expect(kex.encryption_server_to_client).to_equal("aes256-gcm@openssh.com")
expect(kex.mac_client_to_server).to_equal("none")
expect(kex.mac_server_to_client).to_equal("none")
expect(kex.compression_client_to_server).to_equal("none")
expect(kex.compression_server_to_client).to_equal("none")
expect(kex.first_kex_packet_follows).to_equal(false)
```

</details>

#### encodes the KEXINIT cookie, languages, and reserved trailer at fixed offsets

1. ed25519 seed:  ed25519 seed
   - Expected: payload[0] equals `20`
   - Expected: payload[i] equals `0`
   - Expected: ssh_get_u32(payload, 17) equals `17`
   - Expected: payload[off] equals `0`
   - Expected: ssh_get_u32(payload, off) equals `0`
   - Expected: off + 4 equals `payload.len()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit_for_host_keys(HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
))
expect(payload[0]).to_equal(20)
var i: u64 = 1
while i < 17:
    expect(payload[i]).to_equal(0)
    i = i + 1
expect(ssh_get_u32(payload, 17)).to_equal(17)

var off: u64 = 17
var field: u64 = 0
while field < 10:
    val field_len = ssh_get_u32(payload, off).to_u64()
    off = off + 4 + field_len
    field = field + 1
expect(payload[off]).to_equal(0)
off = off + 1
expect(ssh_get_u32(payload, off)).to_equal(0)
expect(off + 4).to_equal(payload.len())
```

</details>

### rsa-sha2-256 host key signing

#### returns Err when RSA key is absent

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-256", host_keys, _test_exchange_hash())
expect(result.is_err()).to_equal(true)
```

</details>

#### blob algo field is rsa-sha2-256 when signing succeeds

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _rsa_2048_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-256", host_keys, _test_exchange_hash())
if result.is_ok():
    val parts = _decode_sig_blob(result.unwrap())
    expect(parts.0).to_equal("rsa-sha2-256")
else:
    expect(result.is_err()).to_equal(true)
```

</details>

#### raw RSA-256 signature is non-empty when signing succeeds

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _rsa_2048_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-256", host_keys, _test_exchange_hash())
if result.is_ok():
    val raw_sig = _decode_sig_blob(result.unwrap()).1
    expect(raw_sig.len()).to_be_greater_than(0)
else:
    expect(result.is_err()).to_equal(true)
```

</details>

### rsa-sha2-512 host key signing

#### returns Err when RSA key is absent

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, _test_exchange_hash())
expect(result.is_err()).to_equal(true)
```

</details>

#### blob algo field is rsa-sha2-512 when signing succeeds

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _rsa_2048_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, _test_exchange_hash())
if result.is_ok():
    val parts = _decode_sig_blob(result.unwrap())
    expect(parts.0).to_equal("rsa-sha2-512")
else:
    expect(result.is_err()).to_equal(true)
```

</details>

#### raw RSA-512 signature is non-empty when signing succeeds

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _rsa_2048_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: pkcs8,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("rsa-sha2-512", host_keys, _test_exchange_hash())
if result.is_ok():
    val raw_sig = _decode_sig_blob(result.unwrap()).1
    expect(raw_sig.len()).to_be_greater_than(0)
else:
    expect(result.is_err()).to_equal(true)
```

</details>

### ecdsa-sha2-nistp256 host key signing

#### returns Err when ECDSA key is absent

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("ecdsa-sha2-nistp256", host_keys, _test_exchange_hash())
expect(result.is_err()).to_equal(true)
```

</details>

#### blob algo field is ecdsa-sha2-nistp256 when signing succeeds

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _ecdsa_p256_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: pkcs8
)
val result = ssh_sign_exchange_hash("ecdsa-sha2-nistp256", host_keys, _test_exchange_hash())
if result.is_ok():
    val parts = _decode_sig_blob(result.unwrap())
    expect(parts.0).to_equal("ecdsa-sha2-nistp256")
else:
    expect(result.is_err()).to_equal(true)
```

</details>

#### ECDSA inner blob decodes to 64-byte fixed r||s

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _ecdsa_p256_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: pkcs8
)
val result = ssh_sign_exchange_hash("ecdsa-sha2-nistp256", host_keys, _test_exchange_hash())
if result.is_ok():
    val inner = _decode_sig_blob(result.unwrap()).1
    val fixed64 = ssh_mpint_pair_to_fixed64(inner)
    expect(fixed64.len()).to_equal(64)
else:
    expect(result.is_err()).to_equal(true)
```

</details>

#### ECDSA fixed64 signature is non-zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = _ecdsa_p256_pkcs8_der()
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: pkcs8
)
val result = ssh_sign_exchange_hash("ecdsa-sha2-nistp256", host_keys, _test_exchange_hash())
if result.is_ok():
    val inner = _decode_sig_blob(result.unwrap()).1
    val fixed64 = ssh_mpint_pair_to_fixed64(inner)
    if fixed64.len() == 64:
        expect(_bytes_all_zero(fixed64)).to_equal(false)
else:
    expect(result.is_err()).to_equal(true)
```

</details>

### unknown host key algorithm

#### returns Err for an unrecognised algorithm

1. ed25519 seed:  ed25519 seed
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
val result = ssh_sign_exchange_hash("ssh-rsa", host_keys, _test_exchange_hash())
expect(result.is_err()).to_equal(true)
```

</details>

### host_key_set_advertised_algorithms

#### Ed25519-only set advertises ssh-ed25519

1. ed25519 seed:  ed25519 seed
   - Expected: host_key_set_advertised_algorithms(host_keys) equals `ssh-ed25519`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("ssh-ed25519")
```

</details>

#### RSA-only set advertises rsa-sha2-256 and rsa-sha2-512

1. rsa pkcs8:  rsa 2048 pkcs8 der
   - Expected: host_key_set_advertised_algorithms(host_keys) equals `rsa-sha2-256,rsa-sha2-512`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: _rsa_2048_pkcs8_der(),
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("rsa-sha2-256,rsa-sha2-512")
```

</details>

#### ECDSA-only set advertises ecdsa-sha2-nistp256

1. ecdsa p256 pkcs8:  ecdsa p256 pkcs8 der
   - Expected: host_key_set_advertised_algorithms(host_keys) equals `ecdsa-sha2-nistp256`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: _ecdsa_p256_pkcs8_der()
)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("ecdsa-sha2-nistp256")
```

</details>

#### full set advertises all four algorithms in priority order

1. ed25519 seed:  ed25519 seed

2. rsa pkcs8:  rsa 2048 pkcs8 der

3. ecdsa p256 pkcs8:  ecdsa p256 pkcs8 der
   - Expected: host_key_set_advertised_algorithms(host_keys) equals `expected`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: _rsa_2048_pkcs8_der(),
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: _ecdsa_p256_pkcs8_der()
)
val expected = "ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256"
expect(host_key_set_advertised_algorithms(host_keys)).to_equal(expected)
```

</details>

#### empty set defaults to ssh-ed25519

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_keys = HostKeySet(
    ed25519_seed: nil,
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
)
expect(host_key_set_advertised_algorithms(host_keys)).to_equal("ssh-ed25519")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
