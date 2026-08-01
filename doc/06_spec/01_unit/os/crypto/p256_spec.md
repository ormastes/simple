# P256 Specification

> <details>

<!-- sdn-diagram:id=p256_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=p256_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

p256_spec -> std
p256_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=p256_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Specification

## Scenarios

### P-256 ECDSA/ECDH — RFC 6979 known-answer tests

#### keygen produces 65-byte uncompressed pubkey

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _rfc6979_privkey()
val pk = p256_keygen(sk)
expect(pk.len()).to_equal(65)
expect(pk[0u64]).to_equal(0x04u8)
```

</details>

#### generated pubkey is on curve

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _rfc6979_privkey()
val pk = p256_keygen(sk)
val px = _get_pubkey_x(pk)
val py = _get_pubkey_y(pk)
expect(p256_point_on_curve(px, py)).to_equal(true)
```

</details>

#### ECDSA sign produces 64-byte signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _rfc6979_privkey()
val msg = _sample_msg()
val msg_hash = sha256(msg)
val sig = p256_ecdsa_sign(sk, msg_hash)
expect(sig.len()).to_equal(64)
```

</details>

#### ECDSA sign matches RFC 6979 r value

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _rfc6979_privkey()
val msg = _sample_msg()
val msg_hash = sha256(msg)
val sig = p256_ecdsa_sign(sk, msg_hash)
val r_bytes = _extract_first_32(sig)
expect(_bytes_hex(r_bytes)).to_equal(
    "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716"
)
```

</details>

#### p256_add(1, 1) mod p == 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val one = _be32_val(0x01u8)
val two_bytes = p256_add(one, one)
val expected = _be32_val(0x02u8)
expect(_bytes_hex(two_bytes)).to_equal(_bytes_hex(expected))
```

</details>

#### p256_mul(2, 3) mod p == 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val two = _be32_val(0x02u8)
val three = _be32_val(0x03u8)
val six_bytes = p256_mul(two, three)
val expected = _be32_val(0x06u8)
expect(_bytes_hex(six_bytes)).to_equal(_bytes_hex(expected))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/p256_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- P-256 ECDSA/ECDH — RFC 6979 known-answer tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
