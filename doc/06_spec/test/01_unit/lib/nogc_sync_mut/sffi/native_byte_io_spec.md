# Native Byte Io Specification

> <details>

<!-- sdn-diagram:id=native_byte_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_byte_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_byte_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_byte_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Byte Io Specification

## Scenarios

### native SFFI [u8] file I/O

#### round-trips a byte pattern by value

- b push
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b: [u8] = []
var i = 0
while i < 6:
    b.push((100 + i) as u8)
    i = i + 1
verify(file_write_bytes("/tmp/svllm_u8_pat.bin", b))
val d = file_read_bytes("/tmp/svllm_u8_pat.bin")
verify(d.len() == 6)
verify((d[0] as i64) == 100)
verify((d[5] as i64) == 105)
```

</details>

#### preserves embedded NUL bytes

- b push
- b push
- b push
- b push
- b push
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b: [u8] = []
b.push(100 as u8)
b.push(0 as u8)
b.push(102 as u8)
b.push(0 as u8)
b.push(255 as u8)
verify(file_write_bytes("/tmp/svllm_u8_nul.bin", b))
val d = file_read_bytes("/tmp/svllm_u8_nul.bin")
verify(d.len() == 5)
verify((d[1] as i64) == 0)
verify((d[2] as i64) == 102)
verify((d[4] as i64) == 255)
```

</details>

#### round-trips all 256 byte values

- b push
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b: [u8] = []
var i = 0
while i < 256:
    b.push((i % 256) as u8)
    i = i + 1
verify(file_write_bytes("/tmp/svllm_u8_full.bin", b))
val d = file_read_bytes("/tmp/svllm_u8_full.bin")
verify(d.len() == 256)
verify((d[0] as i64) == 0)
verify((d[200] as i64) == 200)
verify((d[255] as i64) == 255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/sffi/native_byte_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native SFFI [u8] file I/O

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
