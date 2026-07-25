# Cbor Specification

> <details>

<!-- sdn-diagram:id=cbor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cbor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cbor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cbor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 63 | 63 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Specification

## Scenarios

### CBOR — unsigned integer encode

#### 0 encodes as [0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_zero_ok()).to_equal(true)
```

</details>

#### 23 encodes as [0x17] (max 1-byte inline)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_23_ok()).to_equal(true)
```

</details>

#### 24 encodes as [0x18, 0x18]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_24_ok()).to_equal(true)
```

</details>

#### 255 encodes as [0x18, 0xFF]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_255_ok()).to_equal(true)
```

</details>

#### 256 encodes as [0x19, 0x01, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_256_ok()).to_equal(true)
```

</details>

#### 1000 encodes as [0x19, 0x03, 0xE8]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_1000_ok()).to_equal(true)
```

</details>

#### 65535 encodes as [0x19, 0xFF, 0xFF]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_65535_ok()).to_equal(true)
```

</details>

#### 65536 encodes as 5-byte form

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_uint_65536_ok()).to_equal(true)
```

</details>

### CBOR — signed integer encode (negative)

#### -1 encodes as [0x20]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_minus1_ok()).to_equal(true)
```

</details>

#### -24 encodes as [0x37]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_minus24_ok()).to_equal(true)
```

</details>

#### -25 encodes as [0x38, 0x18]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_minus25_ok()).to_equal(true)
```

</details>

#### -100 encodes as [0x38, 0x63]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_minus100_ok()).to_equal(true)
```

</details>

#### 0 via cbor_encode_int encodes as [0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_pos_zero_ok()).to_equal(true)
```

</details>

#### 1000 via cbor_encode_int encodes same as uint

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_pos_1000_ok()).to_equal(true)
```

</details>

### CBOR — byte string encode

#### empty bytes encodes as [0x40]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_empty_ok()).to_equal(true)
```

</details>

#### 3-byte payload encodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_three_ok()).to_equal(true)
```

</details>

#### 24-byte payload uses 2-byte header

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_24_len_ok()).to_equal(true)
```

</details>

### CBOR — text string encode

#### empty string encodes as [0x60]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_text_empty_ok()).to_equal(true)
```

</details>

#### hello encodes to 6 bytes total

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_text_hello_len_ok()).to_equal(true)
```

</details>

#### hello header byte is 0x65

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_text_hello_header_ok()).to_equal(true)
```

</details>

#### hello payload bytes are correct ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_text_hello_bytes_ok()).to_equal(true)
```

</details>

#### 25-char string uses 2-byte header

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_text_24_len_ok()).to_equal(true)
```

</details>

### CBOR — array header encode

#### count=0 encodes as [0x80]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_empty_ok()).to_equal(true)
```

</details>

#### count=3 encodes as [0x83]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_three_ok()).to_equal(true)
```

</details>

#### count=23 encodes as [0x97]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_23_ok()).to_equal(true)
```

</details>

#### count=24 encodes as [0x98, 0x18]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_24_ok()).to_equal(true)
```

</details>

### CBOR — map header encode

#### count=0 encodes as [0xA0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_map_empty_ok()).to_equal(true)
```

</details>

#### count=2 encodes as [0xA2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_map_two_ok()).to_equal(true)
```

</details>

#### count=24 encodes as [0xB8, 0x18]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_map_24_ok()).to_equal(true)
```

</details>

### CBOR — tag encode

#### tag 0 header starts with [0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tag_0_ok()).to_equal(true)
```

</details>

#### tag 1 header starts with [0xC1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tag_1_ok()).to_equal(true)
```

</details>

#### tag 32 header starts with [0xD8, 0x20]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_tag_32_ok()).to_equal(true)
```

</details>

### CBOR — simple values encode

#### false encodes as [0xF4]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bool_false_ok()).to_equal(true)
```

</details>

#### true encodes as [0xF5]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bool_true_ok()).to_equal(true)
```

</details>

#### null encodes as [0xF6]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_null_ok()).to_equal(true)
```

</details>

#### undefined encodes as [0xF7]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_undefined_ok()).to_equal(true)
```

</details>

### CBOR — decode_int

#### 0 decodes to 0, consumed=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_zero_ok()).to_equal(true)
```

</details>

#### 23 decodes to 23, consumed=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_23_ok()).to_equal(true)
```

</details>

#### 1000 decodes to 1000, consumed=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_1000_ok()).to_equal(true)
```

</details>

#### -1 decodes to -1, consumed=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_minus1_ok()).to_equal(true)
```

</details>

#### -24 decodes to -24, consumed=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_minus24_ok()).to_equal(true)
```

</details>

#### -25 decodes to -25, consumed=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_minus25_ok()).to_equal(true)
```

</details>

#### -100 decodes to -100, consumed=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_di_minus100_ok()).to_equal(true)
```

</details>

### CBOR — decode_text

#### empty string decodes back, consumed=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dt_empty_ok()).to_equal(true)
```

</details>

#### hello decodes back, consumed=6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dt_hello_ok()).to_equal(true)
```

</details>

#### hi decodes back, consumed=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dt_hi_newpos_ok()).to_equal(true)
```

</details>

### CBOR — integer round-trip

#### 0 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_zero_ok()).to_equal(true)
```

</details>

#### 1 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_1_ok()).to_equal(true)
```

</details>

#### 23 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_23_ok()).to_equal(true)
```

</details>

#### 24 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_24_ok()).to_equal(true)
```

</details>

#### 255 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_255_ok()).to_equal(true)
```

</details>

#### 1000 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_1000_ok()).to_equal(true)
```

</details>

#### 65535 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_65535_ok()).to_equal(true)
```

</details>

#### 65536 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_65536_ok()).to_equal(true)
```

</details>

#### -1 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus1_ok()).to_equal(true)
```

</details>

#### -24 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus24_ok()).to_equal(true)
```

</details>

#### -25 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus25_ok()).to_equal(true)
```

</details>

#### -100 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus100_ok()).to_equal(true)
```

</details>

#### -1000 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus1000_ok()).to_equal(true)
```

</details>

### CBOR — negative integer encode (cbor_encode_int for negatives)

#### -1 encodes as [0x20]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_negint_minus1_ok()).to_equal(true)
```

</details>

#### -24 encodes as [0x37]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_negint_minus24_ok()).to_equal(true)
```

</details>

#### -25 encodes as [0x38, 0x18]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_negint_minus25_ok()).to_equal(true)
```

</details>

#### -100 encodes as [0x38, 0x63]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_negint_minus100_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/cbor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CBOR — unsigned integer encode
- CBOR — signed integer encode (negative)
- CBOR — byte string encode
- CBOR — text string encode
- CBOR — array header encode
- CBOR — map header encode
- CBOR — tag encode
- CBOR — simple values encode
- CBOR — decode_int
- CBOR — decode_text
- CBOR — integer round-trip
- CBOR — negative integer encode (cbor_encode_int for negatives)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 63 |
| Active scenarios | 63 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
