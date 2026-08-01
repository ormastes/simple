# Finished App Traffic Specification

> <details>

<!-- sdn-diagram:id=finished_app_traffic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=finished_app_traffic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

finished_app_traffic_spec -> std
finished_app_traffic_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=finished_app_traffic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Finished App Traffic Specification

## Scenarios

### build_finished_bytes wire format

#### emits 0x14 type byte and 3-byte length for SHA-256 verify_data (32B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(32u64, 0xA0u8)
val msg = build_finished_bytes(vd)
# 1B type + 3B length + 32B body
expect(msg.len().to_u64()).to_equal(36u64)
expect(msg[0]).to_equal(0x14u8)
# 24-bit big-endian length encoding 32 → 0x000020
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x20u8)
```

</details>

#### emits 0x14 type byte and 3-byte length for SHA-384 verify_data (48B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(48u64, 0x70u8)
val msg = build_finished_bytes(vd)
# 1B type + 3B length + 48B body
expect(msg.len().to_u64()).to_equal(52u64)
expect(msg[0]).to_equal(0x14u8)
# 24-bit big-endian length encoding 48 → 0x000030
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x30u8)
```

</details>

#### places verify_data immediately after the 4-byte header (32B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(32u64, 0xA0u8)
val msg = build_finished_bytes(vd)
# Spot-check first/middle/last verify_data byte through the wire format
expect(msg[4]).to_equal(vd[0u64])
expect(msg[20]).to_equal(vd[16u64])
expect(msg[35]).to_equal(vd[31u64])
```

</details>

### parse_finished_body identity

#### returns body bytes unchanged for SHA-256 width (32B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(32u64, 0x11u8)
val parsed = parse_finished_body(vd)
expect(parsed.len().to_u64()).to_equal(32u64)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

#### returns body bytes unchanged for SHA-384 width (48B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(48u64, 0x55u8)
val parsed = parse_finished_body(vd)
expect(parsed.len().to_u64()).to_equal(48u64)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

### build → strip-header → parse round-trip

#### round-trips a 32-byte SHA-256 verify_data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(32u64, 0xC3u8)
val msg = build_finished_bytes(vd)
val body = _strip_finished_header(msg)
val parsed = parse_finished_body(body)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

#### round-trips a 48-byte SHA-384 verify_data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vd = _vd_pattern(48u64, 0x7Fu8)
val msg = build_finished_bytes(vd)
val body = _strip_finished_header(msg)
val parsed = parse_finished_body(body)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

### tls13_ct_bytes_equal semantics

#### returns true for identical 32-byte inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(32u64, 0x42u8)
val b = _vd_pattern(32u64, 0x42u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(true)
```

</details>

#### returns true for identical 48-byte inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(48u64, 0x99u8)
val b = _vd_pattern(48u64, 0x99u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(true)
```

</details>

#### returns true for two empty buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(tls13_ct_bytes_equal(empty, empty)).to_equal(true)
```

</details>

#### returns false on a single-bit flip at the FIRST byte (32B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(32u64, 0x42u8)
val b = _flip_byte(a, 0u64, 0x01u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false on a single-bit flip at the LAST byte (32B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(32u64, 0x42u8)
val b = _flip_byte(a, 31u64, 0x80u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false on a single-bit flip at the FIRST byte (48B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(48u64, 0x99u8)
val b = _flip_byte(a, 0u64, 0x01u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false on a single-bit flip at the LAST byte (48B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(48u64, 0x99u8)
val b = _flip_byte(a, 47u64, 0x80u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false when lengths differ (32B vs 48B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(32u64, 0x42u8)
val b = _vd_pattern(48u64, 0x42u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false when lengths differ (empty vs 32B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val b = _vd_pattern(32u64, 0x42u8)
expect(tls13_ct_bytes_equal(empty, b)).to_equal(false)
```

</details>

#### returns false on a multi-byte difference (every byte XORed)

1. b push
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _vd_pattern(32u64, 0x42u8)
var b: [u8] = []
var i: u64 = 0u64
while i < a.len().to_u64():
    b.push(a[i] ^ 0x55u8)
    i = i + 1u64
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/finished_app_traffic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- build_finished_bytes wire format
- parse_finished_body identity
- build → strip-header → parse round-trip
- tls13_ct_bytes_equal semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
