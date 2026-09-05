# Ssh Packet Malformed Specification

> <details>

<!-- sdn-diagram:id=ssh_packet_malformed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_packet_malformed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_packet_malformed_spec -> std
ssh_packet_malformed_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_packet_malformed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Packet Malformed Specification

## Scenarios

### ssh_get_u32_checked bounds

#### returns Err on empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val r = ssh_get_u32_checked(empty, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err on 3-byte input (truncated)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("010203")
val r = ssh_get_u32_checked(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when offset puts read past end

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("0102030405")
# 5 bytes, but reading u32 at offset 3 needs bytes [3..6] — only 2 remain
val r = ssh_get_u32_checked(data, 3)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Ok on exactly 4 bytes at offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("01020304")
val r = ssh_get_u32_checked(data, 0)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap().to_u64()).to_equal(0x01020304)
```

</details>

#### returns Ok when 4 bytes are available at a non-zero offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("AABB00000001CCDD")
val r = ssh_get_u32_checked(data, 2)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap().to_u64()).to_equal(1)
```

</details>

### ssh_get_string bounds

#### returns Err on zero-length input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val r = ssh_get_string(empty, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when only 3 bytes available (truncated length field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("000001")
val r = ssh_get_string(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when declared length exceeds available data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# length field says 10 but only 2 data bytes follow
val data = _hex_decode("0000000A0102")
val r = ssh_get_string(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Ok for a zero-length SSH string (empty content)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("00000000")
val r = ssh_get_string(data, 0)
expect(r.is_ok()).to_equal(true)
val sr = r.unwrap()
expect(sr.data.len()).to_equal(0)
expect(sr.next_offset).to_equal(4)
```

</details>

#### returns Ok and correct content for a 3-byte SSH string

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# length=3, content=0x41 0x42 0x43
val data = _hex_decode("00000003414243")
val r = ssh_get_string(data, 0)
expect(r.is_ok()).to_equal(true)
val sr = r.unwrap()
expect(sr.data.len()).to_equal(3)
expect(_u8_at(sr.data, 0)).to_equal(0x41)
expect(_u8_at(sr.data, 1)).to_equal(0x42)
expect(_u8_at(sr.data, 2)).to_equal(0x43)
expect(sr.next_offset).to_equal(7)
```

</details>

### ssh_packet_read malformed inputs

#### returns Err for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val r = ssh_packet_read(empty, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err for 4-byte input (too short for header)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("0000001C")
val r = ssh_packet_read(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when packet_length is 0 (below minimum of 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("0000000000")
val r = ssh_packet_read(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when packet_length is 1 (below minimum of 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _hex_decode("0000000105")
val r = ssh_packet_read(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when packet_length exceeds SSH_MAX_PACKET (35000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# packet_length = 0x00009000 = 36864 > 35000
val data = _hex_decode("000090000500000000000000000000000000000000000000000000000000000000000000")
val r = ssh_packet_read(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### returns Err when declared packet_length implies more bytes than available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# packet_length = 28 (0x1C) but only 5 bytes supplied
val data = _hex_decode("0000001C05")
val r = ssh_packet_read(data, 0)
expect(r.is_err()).to_equal(true)
```

</details>

#### round-trips a minimal valid packet

- payload push
   - Expected: r.is_ok() is true
   - Expected: pr.packet.payload.len() equals `1`
   - Expected: _u8_at(pr.packet.payload, 0) equals `0x05`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload: [u8] = []
payload.push(0x05)
val packet = ssh_packet_build(payload, 0)
val r = ssh_packet_read(packet, 0)
expect(r.is_ok()).to_equal(true)
val pr = r.unwrap()
expect(pr.packet.payload.len()).to_equal(1)
expect(_u8_at(pr.packet.payload, 0)).to_equal(0x05)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_packet_malformed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ssh_get_u32_checked bounds
- ssh_get_string bounds
- ssh_packet_read malformed inputs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
