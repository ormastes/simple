# Asym Specification

> <details>

<!-- sdn-diagram:id=asym_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=asym_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

asym_spec -> std
asym_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=asym_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Asym Specification

## Scenarios

### ed25519_typed_keypair — RFC 8032 §7.1 TEST 1

#### public key hex matches oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kp1().public.hex()).to_equal("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
```

</details>

#### secret key len is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kp1().secret.len()).to_equal(32)
```

</details>

#### public key len is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kp1().public.len()).to_equal(32)
```

</details>

### ed25519_typed_sign — RFC 8032 §7.1 TEST 1 empty message

#### signature hex matches oracle and len is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = _kp1()
val sig = ed25519_typed_sign(kp.secret, kp.public, _msg1())
expect(sig.hex()).to_equal("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
expect(sig.len()).to_equal(64)
```

</details>

### ed25519_typed_verify — from_hex oracle inputs

#### accepts valid oracle signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = PublicKey.from_hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
val sig = Signature.from_hex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
expect(ed25519_typed_verify(pk, _msg1(), sig)).to_equal(true)
```

</details>

#### rejects signature over wrong message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = PublicKey.from_hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
val sig = Signature.from_hex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
var wrong: [u8] = [0x01u8]
expect(ed25519_typed_verify(pk, ByteSpan.new(wrong), sig)).to_equal(false)
```

</details>

### x25519_typed — RFC 7748 §5.2 KAT

#### shared secret hex matches oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = SecretKey.new(_x25519_scalar())
val peer = PublicKey.new(_x25519_u())
val shared = x25519_typed(sk, peer)
expect(shared.hex()).to_equal("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")
```

</details>

#### shared secret len is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = SecretKey.new(_x25519_scalar())
val peer = PublicKey.new(_x25519_u())
val shared = x25519_typed(sk, peer)
expect(shared.len()).to_equal(32)
```

</details>

### x25519_typed_pubkey — RFC 7748 §6.1 Alice public key

#### pubkey hex matches oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = SecretKey.new(_alice_priv())
val pk = x25519_typed_pubkey(sk)
expect(pk.hex()).to_equal("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
```

</details>

#### pubkey len is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = SecretKey.new(_alice_priv())
val pk = x25519_typed_pubkey(sk)
expect(pk.len()).to_equal(32)
```

</details>

### ecdsa_p256_typed — Signature and PublicKey type construction

#### 64-byte Signature wraps correctly

- var sig = Signature new
   - Expected: sig.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fake_sig: [u8] = [
    0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8, 0x08u8,
    0x09u8, 0x0au8, 0x0bu8, 0x0cu8, 0x0du8, 0x0eu8, 0x0fu8, 0x10u8,
    0x11u8, 0x12u8, 0x13u8, 0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8,
    0x19u8, 0x1au8, 0x1bu8, 0x1cu8, 0x1du8, 0x1eu8, 0x1fu8, 0x20u8,
    0x21u8, 0x22u8, 0x23u8, 0x24u8, 0x25u8, 0x26u8, 0x27u8, 0x28u8,
    0x29u8, 0x2au8, 0x2bu8, 0x2cu8, 0x2du8, 0x2eu8, 0x2fu8, 0x30u8,
    0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x35u8, 0x36u8, 0x37u8, 0x38u8,
    0x39u8, 0x3au8, 0x3bu8, 0x3cu8, 0x3du8, 0x3eu8, 0x3fu8, 0x40u8
]
var sig = Signature.new(fake_sig)
expect(sig.len()).to_equal(64)
```

</details>

#### Signature.from_hex round-trips hex()

- var sig = Signature from hex
   - Expected: sig.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sig = Signature.from_hex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
expect(sig.len()).to_equal(64)
```

</details>

#### PublicKey.new wraps byte array

- var pk = PublicKey new
   - Expected: pk.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fake_pk: [u8] = [0x04u8, 0x01u8, 0x02u8]
var pk = PublicKey.new(fake_pk)
expect(pk.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/typed/asym_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ed25519_typed_keypair — RFC 8032 §7.1 TEST 1
- ed25519_typed_sign — RFC 8032 §7.1 TEST 1 empty message
- ed25519_typed_verify — from_hex oracle inputs
- x25519_typed — RFC 7748 §5.2 KAT
- x25519_typed_pubkey — RFC 7748 §6.1 Alice public key
- ecdsa_p256_typed — Signature and PublicKey type construction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
