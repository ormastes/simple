# Cbor Specification

> Tests covering CBOR — unsigned integer encode, CBOR — signed integer encode (negative), CBOR — byte string encode, CBOR — text string encode, CBOR — array header encode, CBOR — map header encode, CBOR — tag encode, CBOR — simple values encode, CBOR — decode_int, CBOR — decode_text, CBOR — integer round-trip, CBOR — negative integer encode (cbor_encode_int for negatives).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 63 | 63 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Specification

## Scenarios

### CBOR — unsigned integer encode

#### 0 encodes as [0x00]

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 0 encodes as [0x00]
   - Expected: _uint_zero_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 encodes as [0x00]")
expect(_uint_zero_ok()).to_equal(true)
```

</details>

#### 23 encodes as [0x17] (max 1-byte inline)

- 23 encodes as [0x17] (max 1-byte inline)
   - Expected: _uint_23_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("23 encodes as [0x17] (max 1-byte inline)")
expect(_uint_23_ok()).to_equal(true)
```

</details>

#### 24 encodes as [0x18, 0x18]

- 24 encodes as [0x18, 0x18]
   - Expected: _uint_24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("24 encodes as [0x18, 0x18]")
expect(_uint_24_ok()).to_equal(true)
```

</details>

#### 255 encodes as [0x18, 0xFF]

- 255 encodes as [0x18, 0xFF]
   - Expected: _uint_255_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("255 encodes as [0x18, 0xFF]")
expect(_uint_255_ok()).to_equal(true)
```

</details>

#### 256 encodes as [0x19, 0x01, 0x00]

- 256 encodes as [0x19, 0x01, 0x00]
   - Expected: _uint_256_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("256 encodes as [0x19, 0x01, 0x00]")
expect(_uint_256_ok()).to_equal(true)
```

</details>

#### 1000 encodes as [0x19, 0x03, 0xE8]

- 1000 encodes as [0x19, 0x03, 0xE8]
   - Expected: _uint_1000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1000 encodes as [0x19, 0x03, 0xE8]")
expect(_uint_1000_ok()).to_equal(true)
```

</details>

#### 65535 encodes as [0x19, 0xFF, 0xFF]

- 65535 encodes as [0x19, 0xFF, 0xFF]
   - Expected: _uint_65535_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("65535 encodes as [0x19, 0xFF, 0xFF]")
expect(_uint_65535_ok()).to_equal(true)
```

</details>

#### 65536 encodes as 5-byte form

- 65536 encodes as 5-byte form
   - Expected: _uint_65536_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("65536 encodes as 5-byte form")
expect(_uint_65536_ok()).to_equal(true)
```

</details>

### CBOR — signed integer encode (negative)

#### -1 encodes as [0x20]

- -1 encodes as [0x20]
   - Expected: _int_minus1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1 encodes as [0x20]")
expect(_int_minus1_ok()).to_equal(true)
```

</details>

#### -24 encodes as [0x37]

- -24 encodes as [0x37]
   - Expected: _int_minus24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-24 encodes as [0x37]")
expect(_int_minus24_ok()).to_equal(true)
```

</details>

#### -25 encodes as [0x38, 0x18]

- -25 encodes as [0x38, 0x18]
   - Expected: _int_minus25_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-25 encodes as [0x38, 0x18]")
expect(_int_minus25_ok()).to_equal(true)
```

</details>

#### -100 encodes as [0x38, 0x63]

- -100 encodes as [0x38, 0x63]
   - Expected: _int_minus100_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-100 encodes as [0x38, 0x63]")
expect(_int_minus100_ok()).to_equal(true)
```

</details>

#### 0 via cbor_encode_int encodes as [0x00]

- 0 via cbor_encode_int encodes as [0x00]
   - Expected: _int_pos_zero_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 via cbor_encode_int encodes as [0x00]")
expect(_int_pos_zero_ok()).to_equal(true)
```

</details>

#### 1000 via cbor_encode_int encodes same as uint

- 1000 via cbor_encode_int encodes same as uint
   - Expected: _int_pos_1000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1000 via cbor_encode_int encodes same as uint")
expect(_int_pos_1000_ok()).to_equal(true)
```

</details>

### CBOR — byte string encode

#### empty bytes encodes as [0x40]

- empty bytes encodes as [0x40]
   - Expected: _bytes_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty bytes encodes as [0x40]")
expect(_bytes_empty_ok()).to_equal(true)
```

</details>

#### 3-byte payload encodes correctly

- 3-byte payload encodes correctly
   - Expected: _bytes_three_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-byte payload encodes correctly")
expect(_bytes_three_ok()).to_equal(true)
```

</details>

#### 24-byte payload uses 2-byte header

- 24-byte payload uses 2-byte header
   - Expected: _bytes_24_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("24-byte payload uses 2-byte header")
expect(_bytes_24_len_ok()).to_equal(true)
```

</details>

### CBOR — text string encode

#### empty string encodes as [0x60]

- empty string encodes as [0x60]
   - Expected: _text_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string encodes as [0x60]")
expect(_text_empty_ok()).to_equal(true)
```

</details>

#### hello encodes to 6 bytes total

- hello encodes to 6 bytes total
   - Expected: _text_hello_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello encodes to 6 bytes total")
expect(_text_hello_len_ok()).to_equal(true)
```

</details>

#### hello header byte is 0x65

- hello header byte is 0x65
   - Expected: _text_hello_header_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello header byte is 0x65")
expect(_text_hello_header_ok()).to_equal(true)
```

</details>

#### hello payload bytes are correct ASCII

- hello payload bytes are correct ASCII
   - Expected: _text_hello_bytes_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello payload bytes are correct ASCII")
expect(_text_hello_bytes_ok()).to_equal(true)
```

</details>

#### 25-char string uses 2-byte header

- 25-char string uses 2-byte header
   - Expected: _text_24_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("25-char string uses 2-byte header")
expect(_text_24_len_ok()).to_equal(true)
```

</details>

### CBOR — array header encode

#### count=0 encodes as [0x80]

- count=0 encodes as [0x80]
   - Expected: _array_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=0 encodes as [0x80]")
expect(_array_empty_ok()).to_equal(true)
```

</details>

#### count=3 encodes as [0x83]

- count=3 encodes as [0x83]
   - Expected: _array_three_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=3 encodes as [0x83]")
expect(_array_three_ok()).to_equal(true)
```

</details>

#### count=23 encodes as [0x97]

- count=23 encodes as [0x97]
   - Expected: _array_23_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=23 encodes as [0x97]")
expect(_array_23_ok()).to_equal(true)
```

</details>

#### count=24 encodes as [0x98, 0x18]

- count=24 encodes as [0x98, 0x18]
   - Expected: _array_24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=24 encodes as [0x98, 0x18]")
expect(_array_24_ok()).to_equal(true)
```

</details>

### CBOR — map header encode

#### count=0 encodes as [0xA0]

- count=0 encodes as [0xA0]
   - Expected: _map_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=0 encodes as [0xA0]")
expect(_map_empty_ok()).to_equal(true)
```

</details>

#### count=2 encodes as [0xA2]

- count=2 encodes as [0xA2]
   - Expected: _map_two_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=2 encodes as [0xA2]")
expect(_map_two_ok()).to_equal(true)
```

</details>

#### count=24 encodes as [0xB8, 0x18]

- count=24 encodes as [0xB8, 0x18]
   - Expected: _map_24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count=24 encodes as [0xB8, 0x18]")
expect(_map_24_ok()).to_equal(true)
```

</details>

### CBOR — tag encode

#### tag 0 header starts with [0xC0]

- tag 0 header starts with [0xC0]
   - Expected: _tag_0_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tag 0 header starts with [0xC0]")
expect(_tag_0_ok()).to_equal(true)
```

</details>

#### tag 1 header starts with [0xC1]

- tag 1 header starts with [0xC1]
   - Expected: _tag_1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tag 1 header starts with [0xC1]")
expect(_tag_1_ok()).to_equal(true)
```

</details>

#### tag 32 header starts with [0xD8, 0x20]

- tag 32 header starts with [0xD8, 0x20]
   - Expected: _tag_32_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tag 32 header starts with [0xD8, 0x20]")
expect(_tag_32_ok()).to_equal(true)
```

</details>

### CBOR — simple values encode

#### false encodes as [0xF4]

- false encodes as [0xF4]
   - Expected: _bool_false_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false encodes as [0xF4]")
expect(_bool_false_ok()).to_equal(true)
```

</details>

#### true encodes as [0xF5]

- true encodes as [0xF5]
   - Expected: _bool_true_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true encodes as [0xF5]")
expect(_bool_true_ok()).to_equal(true)
```

</details>

#### null encodes as [0xF6]

- null encodes as [0xF6]
   - Expected: _null_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("null encodes as [0xF6]")
expect(_null_ok()).to_equal(true)
```

</details>

#### undefined encodes as [0xF7]

- undefined encodes as [0xF7]
   - Expected: _undefined_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undefined encodes as [0xF7]")
expect(_undefined_ok()).to_equal(true)
```

</details>

### CBOR — decode_int

#### 0 decodes to 0, consumed=1

- 0 decodes to 0, consumed=1
   - Expected: _di_zero_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 decodes to 0, consumed=1")
expect(_di_zero_ok()).to_equal(true)
```

</details>

#### 23 decodes to 23, consumed=1

- 23 decodes to 23, consumed=1
   - Expected: _di_23_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("23 decodes to 23, consumed=1")
expect(_di_23_ok()).to_equal(true)
```

</details>

#### 1000 decodes to 1000, consumed=3

- 1000 decodes to 1000, consumed=3
   - Expected: _di_1000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1000 decodes to 1000, consumed=3")
expect(_di_1000_ok()).to_equal(true)
```

</details>

#### -1 decodes to -1, consumed=1

- -1 decodes to -1, consumed=1
   - Expected: _di_minus1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1 decodes to -1, consumed=1")
expect(_di_minus1_ok()).to_equal(true)
```

</details>

#### -24 decodes to -24, consumed=1

- -24 decodes to -24, consumed=1
   - Expected: _di_minus24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-24 decodes to -24, consumed=1")
expect(_di_minus24_ok()).to_equal(true)
```

</details>

#### -25 decodes to -25, consumed=2

- -25 decodes to -25, consumed=2
   - Expected: _di_minus25_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-25 decodes to -25, consumed=2")
expect(_di_minus25_ok()).to_equal(true)
```

</details>

#### -100 decodes to -100, consumed=2

- -100 decodes to -100, consumed=2
   - Expected: _di_minus100_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-100 decodes to -100, consumed=2")
expect(_di_minus100_ok()).to_equal(true)
```

</details>

### CBOR — decode_text

#### empty string decodes back, consumed=1

- empty string decodes back, consumed=1
   - Expected: _dt_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string decodes back, consumed=1")
expect(_dt_empty_ok()).to_equal(true)
```

</details>

#### hello decodes back, consumed=6

- hello decodes back, consumed=6
   - Expected: _dt_hello_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello decodes back, consumed=6")
expect(_dt_hello_ok()).to_equal(true)
```

</details>

#### hi decodes back, consumed=3

- hi decodes back, consumed=3
   - Expected: _dt_hi_newpos_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hi decodes back, consumed=3")
expect(_dt_hi_newpos_ok()).to_equal(true)
```

</details>

### CBOR — integer round-trip

#### 0 round-trips

- 0 round-trips
   - Expected: _rt_zero_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 round-trips")
expect(_rt_zero_ok()).to_equal(true)
```

</details>

#### 1 round-trips

- 1 round-trips
   - Expected: _rt_1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1 round-trips")
expect(_rt_1_ok()).to_equal(true)
```

</details>

#### 23 round-trips

- 23 round-trips
   - Expected: _rt_23_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("23 round-trips")
expect(_rt_23_ok()).to_equal(true)
```

</details>

#### 24 round-trips

- 24 round-trips
   - Expected: _rt_24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("24 round-trips")
expect(_rt_24_ok()).to_equal(true)
```

</details>

#### 255 round-trips

- 255 round-trips
   - Expected: _rt_255_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("255 round-trips")
expect(_rt_255_ok()).to_equal(true)
```

</details>

#### 1000 round-trips

- 1000 round-trips
   - Expected: _rt_1000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1000 round-trips")
expect(_rt_1000_ok()).to_equal(true)
```

</details>

#### 65535 round-trips

- 65535 round-trips
   - Expected: _rt_65535_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("65535 round-trips")
expect(_rt_65535_ok()).to_equal(true)
```

</details>

#### 65536 round-trips

- 65536 round-trips
   - Expected: _rt_65536_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("65536 round-trips")
expect(_rt_65536_ok()).to_equal(true)
```

</details>

#### -1 round-trips

- -1 round-trips
   - Expected: _rt_minus1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1 round-trips")
expect(_rt_minus1_ok()).to_equal(true)
```

</details>

#### -24 round-trips

- -24 round-trips
   - Expected: _rt_minus24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-24 round-trips")
expect(_rt_minus24_ok()).to_equal(true)
```

</details>

#### -25 round-trips

- -25 round-trips
   - Expected: _rt_minus25_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-25 round-trips")
expect(_rt_minus25_ok()).to_equal(true)
```

</details>

#### -100 round-trips

- -100 round-trips
   - Expected: _rt_minus100_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-100 round-trips")
expect(_rt_minus100_ok()).to_equal(true)
```

</details>

#### -1000 round-trips

- -1000 round-trips
   - Expected: _rt_minus1000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1000 round-trips")
expect(_rt_minus1000_ok()).to_equal(true)
```

</details>

### CBOR — negative integer encode (cbor_encode_int for negatives)

#### -1 encodes as [0x20]

- -1 encodes as [0x20]
   - Expected: _negint_minus1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1 encodes as [0x20]")
expect(_negint_minus1_ok()).to_equal(true)
```

</details>

#### -24 encodes as [0x37]

- -24 encodes as [0x37]
   - Expected: _negint_minus24_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-24 encodes as [0x37]")
expect(_negint_minus24_ok()).to_equal(true)
```

</details>

#### -25 encodes as [0x38, 0x18]

- -25 encodes as [0x38, 0x18]
   - Expected: _negint_minus25_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-25 encodes as [0x38, 0x18]")
expect(_negint_minus25_ok()).to_equal(true)
```

</details>

#### -100 encodes as [0x38, 0x63]

- -100 encodes as [0x38, 0x63]
   - Expected: _negint_minus100_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-100 encodes as [0x38, 0x63]")
expect(_negint_minus100_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/encoding/cbor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR — unsigned integer encode, CBOR — signed integer encode (negative), CBOR — byte string encode, CBOR — text string encode, CBOR — array header encode, CBOR — map header encode, CBOR — tag encode, CBOR — simple values encode, CBOR — decode_int, CBOR — decode_text, CBOR — integer round-trip, CBOR — negative integer encode (cbor_encode_int for negatives).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f25e70d1349d14adc9400ad4a5f697dbab38335e56aa20d39acd1bab0775572`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f25e70d1349d14adc9400ad4a5f697dbab38335e56aa20d39acd1bab0775572`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f25e70d1349d14adc9400ad4a5f697dbab38335e56aa20d39acd1bab0775572`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/encoding/cbor_spec.spl
mirror: doc/06_spec/unit/lib/common/encoding/cbor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/encoding/cbor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/encoding/cbor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/encoding/cbor_spec.spl:389:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0 encodes as [0x00]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/cbor_spec.spl:394:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '23 encodes as [0x17] (max 1-byte inline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/cbor_spec.spl:399:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '24 encodes as [0x18, 0x18]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
