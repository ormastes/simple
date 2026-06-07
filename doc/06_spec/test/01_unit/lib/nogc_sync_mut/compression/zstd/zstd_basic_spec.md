# Zstd Basic Specification

> <details>

<!-- sdn-diagram:id=zstd_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_basic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Basic Specification

## Scenarios

### zstd decoder

#### returns error on empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = zstd_decode([])
expect(result.is_err()).to_equal(true)
```

</details>

#### returns error on bad magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8]
val result = zstd_decode(bad)
expect(result.is_err()).to_equal(true)
```

</details>

#### decodes a single raw block frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content: [u8] = [0x48u8, 0x65u8, 0x6Cu8, 0x6Cu8, 0x6Fu8]  # "Hello"
val frame = make_raw_frame(content)
val result = zstd_decode(frame)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap()
expect(bytes_equal(output, content)).to_equal(true)
```

</details>

#### decodes an empty raw block frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = make_raw_frame([])
val result = zstd_decode(frame)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap()
expect(output.len()).to_equal(0)
```

</details>

#### decodes a single rle block frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = make_rle_frame(0x41, 5)  # 'A' repeated 5 times
val result = zstd_decode(frame)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap()
expect(output.len()).to_equal(5)
var all_a = true
var i = 0
while i < output.len():
    if output[i] != 0x41u8:
        all_a = false
    i = i + 1
expect(all_a).to_equal(true)
```

</details>

#### skips a skippable frame producing empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = make_skippable_frame()
val result = zstd_decode(frame)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap()
expect(output.len()).to_equal(0)
```

</details>

#### decodes chained raw-block frames

1. combined push
2. combined push
   - Expected: result.is_ok() is true
   - Expected: output.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1: [u8] = [0x41u8, 0x42u8]   # "AB"
val c2: [u8] = [0x43u8, 0x44u8]   # "CD"
val f1 = make_raw_frame(c1)
val f2 = make_raw_frame(c2)
var combined: [u8] = []
var i = 0
while i < f1.len():
    combined.push(f1[i])
    i = i + 1
var j = 0
while j < f2.len():
    combined.push(f2[j])
    j = j + 1
val result = zstd_decode(combined)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap()
expect(output.len()).to_equal(4)
```

</details>

#### skippable frame followed by raw block frame

1. combined push
2. combined push
   - Expected: result.is_ok() is true
   - Expected: bytes_equal(output, content) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content: [u8] = [0x58u8, 0x59u8]  # "XY"
val skip = make_skippable_frame()
val data = make_raw_frame(content)
var combined: [u8] = []
var i = 0
while i < skip.len():
    combined.push(skip[i])
    i = i + 1
var j = 0
while j < data.len():
    combined.push(data[j])
    j = j + 1
val result = zstd_decode(combined)
expect(result.is_ok()).to_equal(true)
val output = result.unwrap()
expect(bytes_equal(output, content)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/zstd/zstd_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd decoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
