# Msgpack Specification

> <details>

<!-- sdn-diagram:id=msgpack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=msgpack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

msgpack_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=msgpack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Msgpack Specification

## Scenarios

### MessagePack — nil encode

#### encodes to 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nil_len_ok()).to_equal(true)
```

</details>

#### encodes to byte 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nil_byte_ok()).to_equal(true)
```

</details>

### MessagePack — bool encode

#### false encodes to 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bool_false_len_ok()).to_equal(true)
```

</details>

#### false encodes to 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bool_false_byte_ok()).to_equal(true)
```

</details>

#### true encodes to 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bool_true_len_ok()).to_equal(true)
```

</details>

#### true encodes to 0xC3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bool_true_byte_ok()).to_equal(true)
```

</details>

### MessagePack — integer encode

#### positive fixint

#### 0 encodes as single byte 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_fixpos_zero_ok()).to_equal(true)
```

</details>

#### 127 encodes as single byte 0x7F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_fixpos_max_ok()).to_equal(true)
```

</details>

#### negative fixint

#### -1 encodes as single byte 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_fixneg_minus1_ok()).to_equal(true)
```

</details>

#### -32 encodes as single byte 0xE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_fixneg_minus32_ok()).to_equal(true)
```

</details>

#### uint8

#### 200 encodes as [0xCC, 0xC8]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_uint8_ok()).to_equal(true)
```

</details>

#### uint16

#### 1000 encodes as [0xCD, 0x03, 0xE8]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_uint16_ok()).to_equal(true)
```

</details>

#### int8

#### -50 encodes as [0xD0, 0xCE]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_int8_minus50_ok()).to_equal(true)
```

</details>

#### int16

#### -200 encodes as [0xD1, 0xFF, 0x38]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_int_int16_minus200_ok()).to_equal(true)
```

</details>

### MessagePack — string encode

#### empty string encodes as fixstr [0xA0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_empty_ok()).to_equal(true)
```

</details>

#### hello encodes to 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_hello_len_ok()).to_equal(true)
```

</details>

#### hello header is 0xA5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_hello_header_ok()).to_equal(true)
```

</details>

#### hello payload bytes are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_hello_bytes_ok()).to_equal(true)
```

</details>

#### 32-char string uses str8 format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_32bytes_is_str8()).to_equal(true)
```

</details>

### MessagePack — binary encode

#### empty bin encodes as bin8 [0xC4, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bin_empty_ok()).to_equal(true)
```

</details>

#### 3-byte bin encodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bin_three_bytes_ok()).to_equal(true)
```

</details>

### MessagePack — array/map headers

#### fixarray count=3 is 0x93

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_fixarray_ok()).to_equal(true)
```

</details>

#### fixarray count=15 is 0x9F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_fixarray_max_ok()).to_equal(true)
```

</details>

#### array16 count=16 encodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_array_array16_ok()).to_equal(true)
```

</details>

#### fixmap count=2 is 0x82

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_map_fixmap_ok()).to_equal(true)
```

</details>

#### fixmap count=0 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_map_fixmap_zero_ok()).to_equal(true)
```

</details>

#### map16 count=16 encodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_map_map16_ok()).to_equal(true)
```

</details>

### MessagePack — decode_type

#### nil type tag is 0xC0 and advances by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dtype_nil_ok()).to_equal(true)
```

</details>

#### bool true tag is 0xC3, value=1, advances by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dtype_bool_true_ok()).to_equal(true)
```

</details>

#### fixint 42 tag=42, value=42, advances by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dtype_fixpos_ok()).to_equal(true)
```

</details>

#### negative fixint -5 value=-5, advances by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dtype_fixneg_ok()).to_equal(true)
```

</details>

### MessagePack — decode_str

#### decodes 'hello' back to 'hello'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_str_hello_ok()).to_equal(true)
```

</details>

#### decodes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_str_empty_ok()).to_equal(true)
```

</details>

#### 'hi' advances position by 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decode_str_newpos_ok()).to_equal(true)
```

</details>

### MessagePack — integer round-trip

#### 0 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_zero_ok()).to_equal(true)
```

</details>

#### 127 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_127_ok()).to_equal(true)
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

#### -32 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus32_ok()).to_equal(true)
```

</details>

#### 200 round-trips (uint8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_200_ok()).to_equal(true)
```

</details>

#### 1000 round-trips (uint16)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_1000_ok()).to_equal(true)
```

</details>

#### -50 round-trips (int8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus50_ok()).to_equal(true)
```

</details>

#### -200 round-trips (int16)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_minus200_ok()).to_equal(true)
```

</details>

#### 65535 round-trips (uint16 max)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_65535_ok()).to_equal(true)
```

</details>

#### 70000 round-trips (uint32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_70000_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/msgpack_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MessagePack — nil encode
- MessagePack — bool encode
- MessagePack — integer encode
- MessagePack — string encode
- MessagePack — binary encode
- MessagePack — array/map headers
- MessagePack — decode_type
- MessagePack — decode_str
- MessagePack — integer round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
