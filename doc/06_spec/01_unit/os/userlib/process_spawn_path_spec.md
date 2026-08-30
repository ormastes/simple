# Process Spawn Path Specification

> _Verify sosix_marshal_string_vector produces correct byte layouts._

<!-- sdn-diagram:id=process_spawn_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_spawn_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_spawn_path_spec -> std
process_spawn_path_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_spawn_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Spawn Path Specification

## Scenarios

### spawn_path marshaling
_Verify sosix_marshal_string_vector produces correct byte layouts._

#### returns empty buffer for empty input

1. expect buf len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_empty_buf()
expect buf.len() == 0
```

</details>

#### marshals single string with correct total size

1. expect buf len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_single_string_buf()
# "hello" = 5 bytes + 1 NUL + 1 offset (8 bytes) + NULL terminator (8 bytes)
# = 6 + 16 = 22
val expected = _expected_size(1, 5)
expect expected == 22
expect buf.len().to_u64() == expected
```

</details>

#### places NUL terminator after string bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_single_string_buf()
# buf[0..4] = "hello", buf[5] = 0x00
expect buf[0] == 0x68u8  # 'h'
expect buf[1] == 0x65u8  # 'e'
expect buf[2] == 0x6Cu8  # 'l'
expect buf[3] == 0x6Cu8  # 'l'
expect buf[4] == 0x6Fu8  # 'o'
expect buf[5] == 0x00u8  # NUL
```

</details>

#### encodes offset 0 for first string in pointer table

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_single_string_buf()
# Offset table starts at byte 6 (after "hello\0")
# First offset = 0, little-endian u64
expect buf[6] == 0x00u8
expect buf[7] == 0x00u8
expect buf[8] == 0x00u8
expect buf[9] == 0x00u8
expect buf[10] == 0x00u8
expect buf[11] == 0x00u8
expect buf[12] == 0x00u8
expect buf[13] == 0x00u8
```

</details>

#### ends with 8-byte NULL terminator pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_single_string_buf()
val n = buf.len()
# Last 8 bytes should all be zero
expect buf[n - 1] == 0x00u8
expect buf[n - 2] == 0x00u8
expect buf[n - 3] == 0x00u8
expect buf[n - 4] == 0x00u8
expect buf[n - 5] == 0x00u8
expect buf[n - 6] == 0x00u8
expect buf[n - 7] == 0x00u8
expect buf[n - 8] == 0x00u8
```

</details>

#### marshals two strings with correct total size

1. expect buf len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_two_string_buf()
# "ab" (2+1) + "cde" (3+1) = 7 string bytes
# + 2 offsets (16) + NULL ptr (8) = 31
val expected = _expected_size(2, 5)
expect expected == 31
expect buf.len().to_u64() == expected
```

</details>

#### encodes second string offset correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_two_string_buf()
# String data: "ab\0cde\0" = 7 bytes
# Offset table starts at byte 7
# offset[0] = 0  (bytes 7..14)
# offset[1] = 3  (bytes 15..22) — "ab\0" is 3 bytes
expect buf[15] == 0x03u8  # offset = 3, low byte
expect buf[16] == 0x00u8
```

</details>

#### preserves string content for two-element vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_two_string_buf()
# "ab" at offset 0
expect buf[0] == 0x61u8  # 'a'
expect buf[1] == 0x62u8  # 'b'
expect buf[2] == 0x00u8  # NUL
# "cde" at offset 3
expect buf[3] == 0x63u8  # 'c'
expect buf[4] == 0x64u8  # 'd'
expect buf[5] == 0x65u8  # 'e'
expect buf[6] == 0x00u8  # NUL
```

</details>

### spawn_path API
_Verify spawn_path error handling, argv defaults, and type signatures._

#### returns Err(EINVAL) for empty path

1. expect result is err
2. expect result unwrap err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spawn_path("", [], [])
expect result.is_err() == true
expect result.unwrap_err() == 22
```

</details>

#### returns Err(EINVAL) for empty path with argv

1. expect result is err
2. expect result unwrap err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spawn_path("", ["arg0"], ["HOME=/home"])
expect result.is_err() == true
expect result.unwrap_err() == 22
```

</details>

#### sosix_marshal_string_vector accepts [text] and returns [u8]

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input: [text] = ["test"]
val result: [u8] = sosix_marshal_string_vector(input)
expect result.len() > 0
```

</details>

#### sosix_marshal_string_vector_size returns u64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size: u64 = sosix_marshal_string_vector_size(2, 10)
# total_bytes(10) + count(2) + (count+1)*8 = 10 + 2 + 24 = 36
expect size == 36
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/userlib/process_spawn_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spawn_path marshaling
- spawn_path API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
