# OS rt_ed25519_sign Specification

> Tests the freshly-added `rt_ed25519_sign` SFFI and its `ed25519_sign_pkcs8` Tier-2 wrapper (RFC 8032 / EdDSA over Curve25519).

<!-- sdn-diagram:id=os_rt_ed25519_sign_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_rt_ed25519_sign_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_rt_ed25519_sign_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_rt_ed25519_sign_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OS rt_ed25519_sign Specification

Tests the freshly-added `rt_ed25519_sign` SFFI and its `ed25519_sign_pkcs8` Tier-2 wrapper (RFC 8032 / EdDSA over Curve25519).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/os/os_rt_ed25519_sign_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the freshly-added `rt_ed25519_sign` SFFI and its `ed25519_sign_pkcs8` Tier-2
wrapper (RFC 8032 / EdDSA over Curve25519).

Covers:
  1. Round-trip: sign -> verify (64-byte sig, verify = true)
  2. Determinism: same key+msg signed twice gives byte-identical results
  3. Malformed PKCS#8 returns empty array
  4. One-bit flip in signature fails verification
  5. (Optional, openssl-gated) Simple sign -> openssl pkeyutl verify

tag: slow, system, crypto

## Scenarios

### os_rt_ed25519_sign: round-trip sign -> verify

#### ed25519_sign_pkcs8 round-trips through ed25519_verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8  = hex_to_bytes(ED25519_PKCS8_HEX)
val pubkey = hex_to_bytes(ED25519_PUBKEY_HEX)
val msg    = _msg_hello()
val sig    = ed25519_sign_pkcs8(pkcs8, msg)
expect(sig.len()).to_equal(64)
val ok = ed25519_verify(pubkey, msg, sig)
expect(ok).to_equal(true)
```

</details>

#### ed25519_sign round-trips for empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8  = hex_to_bytes(ED25519_PKCS8_HEX)
val pubkey = hex_to_bytes(ED25519_PUBKEY_HEX)
var msg: [u8] = []
val sig = ed25519_sign_pkcs8(pkcs8, msg)
expect(sig.len()).to_equal(64)
val ok = ed25519_verify(pubkey, msg, sig)
expect(ok).to_equal(true)
```

</details>

### os_rt_ed25519_sign: determinism (RFC 8032)

#### ed25519_sign_pkcs8 is deterministic for same key + message

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8 = hex_to_bytes(ED25519_PKCS8_HEX)
val msg   = _msg_hello()
val sig1  = ed25519_sign_pkcs8(pkcs8, msg)
val sig2  = ed25519_sign_pkcs8(pkcs8, msg)
expect(sig1.len()).to_equal(64)
expect(sig2.len()).to_equal(64)
expect(_bytes_eq(sig1, sig2)).to_equal(true)
```

</details>

### os_rt_ed25519_sign: malformed input contract

#### ed25519_sign_pkcs8 returns empty [u8] on malformed pkcs8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_pkcs8 = hex_to_bytes(BAD_PKCS8_HEX)
val msg       = _msg_hello()
val bad_sig   = ed25519_sign_pkcs8(bad_pkcs8, msg)
expect(bad_sig.len()).to_equal(0)
```

</details>

#### ed25519_sign_pkcs8 returns empty [u8] on junk raw bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val junk: [u8] = [0x30u8, 0x01, 0x00]
val msg = _msg_hello()
val bad_sig = ed25519_sign_pkcs8(junk, msg)
expect(bad_sig.len()).to_equal(0)
```

</details>

### os_rt_ed25519_sign: signature integrity (one-bit flip)

#### ed25519_verify rejects signature with one-byte flip (first byte)

1. bad sig push
2. bad sig push
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8  = hex_to_bytes(ED25519_PKCS8_HEX)
val pubkey = hex_to_bytes(ED25519_PUBKEY_HEX)
val msg    = _msg_hello()
val sig    = ed25519_sign_pkcs8(pkcs8, msg)
expect(sig.len()).to_equal(64)
# Build corrupted signature: flip first byte
var bad_sig: [u8] = []
bad_sig.push(sig[0] ^ 0xFF)
var i: u64 = 1
while i < sig.len():
    bad_sig.push(sig[i])
    i = i + 1
val ok = ed25519_verify(pubkey, msg, bad_sig)
expect(ok).to_equal(false)
```

</details>

#### ed25519_verify rejects signature with one-byte flip (last byte)

1. bad sig push
2. bad sig push
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkcs8  = hex_to_bytes(ED25519_PKCS8_HEX)
val pubkey = hex_to_bytes(ED25519_PUBKEY_HEX)
val msg    = _msg_hello()
val sig    = ed25519_sign_pkcs8(pkcs8, msg)
expect(sig.len()).to_equal(64)
# Build corrupted signature: flip last byte
var bad_sig: [u8] = []
var i: u64 = 0
while i < 63:
    bad_sig.push(sig[i])
    i = i + 1
bad_sig.push(sig[63] ^ 0x01)
val ok = ed25519_verify(pubkey, msg, bad_sig)
expect(ok).to_equal(false)
```

</details>

### os_rt_ed25519_sign: openssl cross-check

#### Simple ed25519_sign_pkcs8 -> openssl pkeyutl -verify -> success

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not openssl_present():
    val pkcs8 = hex_to_bytes(ED25519_PKCS8_HEX)
    val pubkey = hex_to_bytes(ED25519_PUBKEY_HEX)
    val msg   = _msg_hello()
    val sig   = ed25519_sign_pkcs8(pkcs8, msg)
    expect(sig.len()).to_equal(64)
    val ok = ed25519_verify(pubkey, msg, sig)
    expect(ok).to_equal(true)
else:
    val pkcs8 = hex_to_bytes(ED25519_PKCS8_HEX)
    val spki  = hex_to_bytes(ED25519_SPKI_HEX)
    val msg   = _msg_hello()
    val sig   = ed25519_sign_pkcs8(pkcs8, msg)
    expect(sig.len()).to_equal(64)
    val ok = _openssl_ed25519_verify(spki, msg, sig)
    expect(ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
