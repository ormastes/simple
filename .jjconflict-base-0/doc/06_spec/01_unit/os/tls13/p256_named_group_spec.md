# P256 Named Group Specification

> <details>

<!-- sdn-diagram:id=p256_named_group_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=p256_named_group_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

p256_named_group_spec -> std
p256_named_group_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=p256_named_group_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Named Group Specification

## Scenarios

### secp256r1 NamedGroup constant

#### GROUP_SECP256R1 equals IANA value 0x0017 (RFC 8422 §5.1.1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GROUP_SECP256R1).to_equal(0x0017u16)
```

</details>

#### GROUP_X25519 equals IANA value 0x001D (RFC 8446 §4.2.7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GROUP_X25519).to_equal(0x001Du16)
```

</details>

### key_share extension dual entry construction

#### ClientHello with p256_pub contains an X25519 KeyShareEntry (group 0x001D, key_len 32)

1.  ch random


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p256 = p256_keypair_pub(_scalar_one())
val ch = build_client_hello_bytes_with_p256(
    _ch_random(), _x25519_pub_fixture(), p256, "example.com")
val off = _find_key_share_entry(ch, 0x00u8, 0x1Du8, 32u64)
# >= 0 means the entry was located in the wire; -1 means absent.
expect(off).to_be_greater_than(-1i64)
```

</details>

#### ClientHello with p256_pub contains a secp256r1 KeyShareEntry (group 0x0017, key_len 65)

1.  ch random


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p256 = p256_keypair_pub(_scalar_one())
val ch = build_client_hello_bytes_with_p256(
    _ch_random(), _x25519_pub_fixture(), p256, "example.com")
val off = _find_key_share_entry(ch, 0x00u8, 0x17u8, 65u64)
expect(off).to_be_greater_than(-1i64)
```

</details>

#### secp256r1 KeyShareEntry payload begins with the SEC1 uncompressed-point tag 0x04

1.  ch random
   - Expected: ch[payload_start] equals `0x04u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p256 = p256_keypair_pub(_scalar_one())
val ch = build_client_hello_bytes_with_p256(
    _ch_random(), _x25519_pub_fixture(), p256, "example.com")
val off = _find_key_share_entry(ch, 0x00u8, 0x17u8, 65u64)
# off must be a valid byte index for the indexing below to be meaningful.
expect(off).to_be_greater_than(-1i64)
val payload_start = off.to_u64()
expect(ch[payload_start]).to_equal(0x04u8)
```

</details>

#### supported_groups extension advertises secp256r1 (0x0017) somewhere in ClientHello

1.  ch random


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Count occurrences of the 0x00 0x17 byte pair in the ClientHello.
# secp256r1 (0x0017) must appear at least once (in supported_groups,
# plus once more in the key_share group field).
val p256 = p256_keypair_pub(_scalar_one())
val ch = build_client_hello_bytes_with_p256(
    _ch_random(), _x25519_pub_fixture(), p256, "example.com")
val occurrences = _count_byte_pair(ch, 0x00u8, 0x17u8)
expect(occurrences).to_be_greater_than(0u64)
```

</details>

#### back-compat: build_client_hello_bytes (no p256) still advertises secp256r1 in supported_groups

1.  ch random


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = build_client_hello_bytes(
    _ch_random(), _x25519_pub_fixture(), "example.com")
expect(ch.len()).to_be_greater_than(0u64)
# supported_groups now lists secp256r1 even when no P-256 key_share
# is sent — this is what enables a server to issue an HRR asking for
# secp256r1 in CH2.
val occurrences = _count_byte_pair(ch, 0x00u8, 0x17u8)
expect(occurrences).to_be_greater_than(0u64)
```

</details>

### P-256 ephemeral keypair gen smoke

#### p256_keypair_pub returns a 65-byte uncompressed SEC1 point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = p256_keypair_pub(_scalar_one())
expect(out.len()).to_equal(65u64)
```

</details>

#### p256_keypair_pub starts with the uncompressed-point tag 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = p256_keypair_pub(_scalar_one())
expect(out[0u64]).to_equal(0x04u8)
```

</details>

#### p256_keypair_pub(k=1) X-coordinate equals SEC2 generator Gx (smoke: scalar mult is on-curve)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# k=1 => k*G = G. Byte-equality of the output X against the public
# SEC2 / FIPS 186-4 D.2.3 base point is the strongest cheap smoke
# check that the scalar-mult ladder lands on the curve.
val out = p256_keypair_pub(_scalar_one())
val out_x = _slice32(out, 1u64)
expect(out_x).to_equal(_gx_bytes())
```

</details>

#### p256_keypair_pub(k=1) Y-coordinate equals SEC2 generator Gy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = p256_keypair_pub(_scalar_one())
val out_y = _slice32(out, 33u64)
expect(out_y).to_equal(_gy_bytes())
```

</details>

#### p256_keypair_pub(k=2) X-coordinate differs from Gx (smoke: doubling actually fires)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2G != G; if doubling were a no-op the X-coordinate would still equal
# Gx. _bytes_equal gives us a direct value comparison rather than a
# boolean-wrapper assertion.
val out2 = p256_keypair_pub(_scalar_two())
val out2_x = _slice32(out2, 1u64)
expect(_bytes_equal(out2_x, _gx_bytes())).to_equal(false)
```

</details>

#### p256_keypair_pub(k=2) returns a 65-byte SEC1 uncompressed point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out2 = p256_keypair_pub(_scalar_two())
expect(out2.len()).to_equal(65u64)
expect(out2[0u64]).to_equal(0x04u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/p256_named_group_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- secp256r1 NamedGroup constant
- key_share extension dual entry construction
- P-256 ephemeral keypair gen smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
