# P384 Specification

> <details>

<!-- sdn-diagram:id=p384_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=p384_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

p384_spec -> std
p384_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=p384_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P384 Specification

## Scenarios

### P-384

#### field add and mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val one = _be48_val(0x01)
val two_bytes = p384_add(one, one)
val two = _be48_val(0x02)
expect(_bytes_hex(two_bytes)).to_equal(_bytes_hex(two))
val three = _be48_val(0x03)
val six_bytes = p384_mul(two, three)
val six = _be48_val(0x06)
expect(_bytes_hex(six_bytes)).to_equal(_bytes_hex(six))
```

</details>

#### Generator G is on the P-384 curve

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(p384_point_on_curve(_gx_bytes(), _gy_bytes())).to_equal(true)
```

</details>

#### scalar multiplication matches exact public-key KAT for k=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k1_pub = p384_scalar_mult(_be48_val(0x01), _gx_bytes(), _gy_bytes())
expect(_bytes_hex(k1_pub)).to_equal(_pub_hex_k1())
```

</details>

#### scalar multiplication matches exact public-key KAT for k=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k2_pub = p384_scalar_mult(_be48_val(0x02), _gx_bytes(), _gy_bytes())
expect(_bytes_hex(k2_pub)).to_equal(_pub_hex_k2())
```

</details>

#### scalar multiplication matches exact public-key KAT for k=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k3_pub = p384_scalar_mult(_be48_val(0x03), _gx_bytes(), _gy_bytes())
expect(_bytes_hex(k3_pub)).to_equal(_pub_hex_k3())
```

</details>

#### keygen matches exact public-key KAT for seeded private key 0x6B

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(p384_keygen(_make_key(0x6B)))).to_equal(_pub_hex_alice())
```

</details>

#### keygen matches exact public-key KAT for seeded private key 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(p384_keygen(_make_key(0x01)))).to_equal(_pub_hex_bob())
```

</details>

#### keygen and ECDSA sign-verify round trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _make_key(0x6B)
val pub_key = p384_keygen(sk)
expect(pub_key.len()).to_equal(97)
expect(pub_key[0u64]).to_equal(0x04u8)
val msg_hash = sha384(_make_key(0x01))
val sig = p384_ecdsa_sign(sk, msg_hash)
expect(sig.len()).to_equal(96)
expect(p384_ecdsa_verify(pub_key, msg_hash, sig)).to_equal(true)
```

</details>

#### ECDH commutativity

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alice_priv = _make_key(0x6B)
val bob_priv = _make_key(0x01)
val alice_pub = p384_keygen(alice_priv)
val bob_pub = p384_keygen(bob_priv)
val shared_ab = p384_ecdh(alice_priv, bob_pub)
val shared_ba = p384_ecdh(bob_priv, alice_pub)
expect(_bytes_hex(shared_ab)).to_equal(_bytes_hex(shared_ba))
expect(_bytes_hex(shared_ab)).to_equal(_shared_hex_alice_bob())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/p384_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- P-384

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
