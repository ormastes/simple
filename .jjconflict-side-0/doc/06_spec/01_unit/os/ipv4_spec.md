# Ipv4 Specification

> <details>

<!-- sdn-diagram:id=ipv4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipv4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipv4_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipv4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipv4 Specification

## Scenarios

### IPv4 address (RFC 791)

#### formats dotted decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ipv4Address.from_bytes(192u8, 168u8, 1u8, 1u8).to_text()).to_equal("192.168.1.1")
```

</details>

#### round-trips octets through to_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = Ipv4Address.from_bytes(192u8, 168u8, 1u8, 1u8).to_bytes()
expect(b[0].to_i64()).to_equal(192)
expect(b[3].to_i64()).to_equal(1)
```

</details>

<details>
<summary>Advanced: detects loopback 127.x.x.x</summary>

#### detects loopback 127.x.x.x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ipv4Address.from_bytes(127u8, 0u8, 0u8, 1u8).is_loopback()).to_equal(true)
```

</details>


</details>

#### detects limited broadcast

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Ipv4Address.broadcast_all().is_broadcast()).to_equal(true)
```

</details>

#### matches subnet membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Ipv4Address.from_bytes(192u8, 168u8, 1u8, 5u8)
val net = Ipv4Address.from_bytes(192u8, 168u8, 1u8, 0u8)
val mask = Ipv4Address.from_bytes(255u8, 255u8, 255u8, 0u8)
expect(a.in_subnet(net, mask)).to_equal(true)
```

</details>

### IPv4 header checksum (RFC 1071)

#### computes the canonical 0xb861 vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ipv4_checksum(_canonical_header()).to_i64()).to_equal(47201)
```

</details>

### IPv4 build/parse round-trip (RFC 791)

#### preserves protocol

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_protocol()).to_equal(17)
```

</details>

#### preserves source address

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_src_text()).to_equal("10.0.0.1")
```

</details>

#### preserves destination address

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_dst_text()).to_equal("10.0.0.2")
```

</details>

#### preserves payload length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_payload_len()).to_equal(4)
```

</details>

#### preserves payload bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_payload_first()).to_equal(222)
```

</details>

#### rejects a truncated packet

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_too_short()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/ipv4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPv4 address (RFC 791)
- IPv4 header checksum (RFC 1071)
- IPv4 build/parse round-trip (RFC 791)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
