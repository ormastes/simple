# Msgpack Specification

> Tests covering MessagePack — nil encode, MessagePack — bool encode, MessagePack — integer encode, MessagePack — string encode, MessagePack — binary encode, MessagePack — array/map headers, MessagePack — decode_type, MessagePack — decode_str, MessagePack — integer round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Msgpack Specification

## Scenarios

### MessagePack — nil encode

#### encodes to 1 byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes to 1 byte
   - Expected: _nil_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes to 1 byte")
expect(_nil_len_ok()).to_equal(true)
```

</details>

#### encodes to byte 0xC0

- encodes to byte 0xC0
   - Expected: _nil_byte_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes to byte 0xC0")
expect(_nil_byte_ok()).to_equal(true)
```

</details>

### MessagePack — bool encode

#### false encodes to 1 byte

- false encodes to 1 byte
   - Expected: _bool_false_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false encodes to 1 byte")
expect(_bool_false_len_ok()).to_equal(true)
```

</details>

#### false encodes to 0xC2

- false encodes to 0xC2
   - Expected: _bool_false_byte_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false encodes to 0xC2")
expect(_bool_false_byte_ok()).to_equal(true)
```

</details>

#### true encodes to 1 byte

- true encodes to 1 byte
   - Expected: _bool_true_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true encodes to 1 byte")
expect(_bool_true_len_ok()).to_equal(true)
```

</details>

#### true encodes to 0xC3

- true encodes to 0xC3
   - Expected: _bool_true_byte_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true encodes to 0xC3")
expect(_bool_true_byte_ok()).to_equal(true)
```

</details>

### MessagePack — integer encode

#### positive fixint

#### 0 encodes as single byte 0x00

- 0 encodes as single byte 0x00
   - Expected: _int_fixpos_zero_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 encodes as single byte 0x00")
expect(_int_fixpos_zero_ok()).to_equal(true)
```

</details>

#### 127 encodes as single byte 0x7F

- 127 encodes as single byte 0x7F
   - Expected: _int_fixpos_max_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("127 encodes as single byte 0x7F")
expect(_int_fixpos_max_ok()).to_equal(true)
```

</details>

#### negative fixint

#### -1 encodes as single byte 0xFF

- -1 encodes as single byte 0xFF
   - Expected: _int_fixneg_minus1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1 encodes as single byte 0xFF")
expect(_int_fixneg_minus1_ok()).to_equal(true)
```

</details>

#### -32 encodes as single byte 0xE0

- -32 encodes as single byte 0xE0
   - Expected: _int_fixneg_minus32_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-32 encodes as single byte 0xE0")
expect(_int_fixneg_minus32_ok()).to_equal(true)
```

</details>

#### uint8

#### 200 encodes as [0xCC, 0xC8]

- 200 encodes as [0xCC, 0xC8]
   - Expected: _int_uint8_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("200 encodes as [0xCC, 0xC8]")
expect(_int_uint8_ok()).to_equal(true)
```

</details>

#### uint16

#### 1000 encodes as [0xCD, 0x03, 0xE8]

- 1000 encodes as [0xCD, 0x03, 0xE8]
   - Expected: _int_uint16_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1000 encodes as [0xCD, 0x03, 0xE8]")
expect(_int_uint16_ok()).to_equal(true)
```

</details>

#### int8

#### -50 encodes as [0xD0, 0xCE]

- -50 encodes as [0xD0, 0xCE]
   - Expected: _int_int8_minus50_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-50 encodes as [0xD0, 0xCE]")
expect(_int_int8_minus50_ok()).to_equal(true)
```

</details>

#### int16

#### -200 encodes as [0xD1, 0xFF, 0x38]

- -200 encodes as [0xD1, 0xFF, 0x38]
   - Expected: _int_int16_minus200_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-200 encodes as [0xD1, 0xFF, 0x38]")
expect(_int_int16_minus200_ok()).to_equal(true)
```

</details>

### MessagePack — string encode

#### empty string encodes as fixstr [0xA0]

- empty string encodes as fixstr [0xA0]
   - Expected: _str_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string encodes as fixstr [0xA0]")
expect(_str_empty_ok()).to_equal(true)
```

</details>

#### hello encodes to 6 bytes

- hello encodes to 6 bytes
   - Expected: _str_hello_len_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello encodes to 6 bytes")
expect(_str_hello_len_ok()).to_equal(true)
```

</details>

#### hello header is 0xA5

- hello header is 0xA5
   - Expected: _str_hello_header_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello header is 0xA5")
expect(_str_hello_header_ok()).to_equal(true)
```

</details>

#### hello payload bytes are correct

- hello payload bytes are correct
   - Expected: _str_hello_bytes_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hello payload bytes are correct")
expect(_str_hello_bytes_ok()).to_equal(true)
```

</details>

#### 32-char string uses str8 format

- 32-char string uses str8 format
   - Expected: _str_32bytes_is_str8() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("32-char string uses str8 format")
expect(_str_32bytes_is_str8()).to_equal(true)
```

</details>

### MessagePack — binary encode

#### empty bin encodes as bin8 [0xC4, 0x00]

- empty bin encodes as bin8 [0xC4, 0x00]
   - Expected: _bin_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty bin encodes as bin8 [0xC4, 0x00]")
expect(_bin_empty_ok()).to_equal(true)
```

</details>

#### 3-byte bin encodes correctly

- 3-byte bin encodes correctly
   - Expected: _bin_three_bytes_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-byte bin encodes correctly")
expect(_bin_three_bytes_ok()).to_equal(true)
```

</details>

### MessagePack — array/map headers

#### fixarray count=3 is 0x93

- fixarray count=3 is 0x93
   - Expected: _array_fixarray_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixarray count=3 is 0x93")
expect(_array_fixarray_ok()).to_equal(true)
```

</details>

#### fixarray count=15 is 0x9F

- fixarray count=15 is 0x9F
   - Expected: _array_fixarray_max_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixarray count=15 is 0x9F")
expect(_array_fixarray_max_ok()).to_equal(true)
```

</details>

#### array16 count=16 encodes correctly

- array16 count=16 encodes correctly
   - Expected: _array_array16_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array16 count=16 encodes correctly")
expect(_array_array16_ok()).to_equal(true)
```

</details>

#### fixmap count=2 is 0x82

- fixmap count=2 is 0x82
   - Expected: _map_fixmap_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixmap count=2 is 0x82")
expect(_map_fixmap_ok()).to_equal(true)
```

</details>

#### fixmap count=0 is 0x80

- fixmap count=0 is 0x80
   - Expected: _map_fixmap_zero_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixmap count=0 is 0x80")
expect(_map_fixmap_zero_ok()).to_equal(true)
```

</details>

#### map16 count=16 encodes correctly

- map16 count=16 encodes correctly
   - Expected: _map_map16_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("map16 count=16 encodes correctly")
expect(_map_map16_ok()).to_equal(true)
```

</details>

### MessagePack — decode_type

#### nil type tag is 0xC0 and advances by 1

- nil type tag is 0xC0 and advances by 1
   - Expected: _dtype_nil_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil type tag is 0xC0 and advances by 1")
expect(_dtype_nil_ok()).to_equal(true)
```

</details>

#### bool true tag is 0xC3, value=1, advances by 1

- bool true tag is 0xC3, value=1, advances by 1
   - Expected: _dtype_bool_true_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool true tag is 0xC3, value=1, advances by 1")
expect(_dtype_bool_true_ok()).to_equal(true)
```

</details>

#### fixint 42 tag=42, value=42, advances by 1

- fixint 42 tag=42, value=42, advances by 1
   - Expected: _dtype_fixpos_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixint 42 tag=42, value=42, advances by 1")
expect(_dtype_fixpos_ok()).to_equal(true)
```

</details>

#### negative fixint -5 value=-5, advances by 1

- negative fixint -5 value=-5, advances by 1
   - Expected: _dtype_fixneg_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative fixint -5 value=-5, advances by 1")
expect(_dtype_fixneg_ok()).to_equal(true)
```

</details>

### MessagePack — decode_str

#### decodes 'hello' back to 'hello'

- decodes 'hello' back to 'hello'
   - Expected: _decode_str_hello_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes 'hello' back to 'hello'")
expect(_decode_str_hello_ok()).to_equal(true)
```

</details>

#### decodes empty string

- decodes empty string
   - Expected: _decode_str_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes empty string")
expect(_decode_str_empty_ok()).to_equal(true)
```

</details>

#### 'hi' advances position by 3

- 'hi' advances position by 3
   - Expected: _decode_str_newpos_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'hi' advances position by 3")
expect(_decode_str_newpos_ok()).to_equal(true)
```

</details>

### MessagePack — integer round-trip

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

#### 127 round-trips

- 127 round-trips
   - Expected: _rt_127_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("127 round-trips")
expect(_rt_127_ok()).to_equal(true)
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

#### -32 round-trips

- -32 round-trips
   - Expected: _rt_minus32_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-32 round-trips")
expect(_rt_minus32_ok()).to_equal(true)
```

</details>

#### 200 round-trips (uint8)

- 200 round-trips (uint8)
   - Expected: _rt_200_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("200 round-trips (uint8)")
expect(_rt_200_ok()).to_equal(true)
```

</details>

#### 1000 round-trips (uint16)

- 1000 round-trips (uint16)
   - Expected: _rt_1000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1000 round-trips (uint16)")
expect(_rt_1000_ok()).to_equal(true)
```

</details>

#### -50 round-trips (int8)

- -50 round-trips (int8)
   - Expected: _rt_minus50_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-50 round-trips (int8)")
expect(_rt_minus50_ok()).to_equal(true)
```

</details>

#### -200 round-trips (int16)

- -200 round-trips (int16)
   - Expected: _rt_minus200_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-200 round-trips (int16)")
expect(_rt_minus200_ok()).to_equal(true)
```

</details>

#### 65535 round-trips (uint16 max)

- 65535 round-trips (uint16 max)
   - Expected: _rt_65535_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("65535 round-trips (uint16 max)")
expect(_rt_65535_ok()).to_equal(true)
```

</details>

#### 70000 round-trips (uint32)

- 70000 round-trips (uint32)
   - Expected: _rt_70000_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("70000 round-trips (uint32)")
expect(_rt_70000_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/encoding/msgpack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MessagePack — nil encode, MessagePack — bool encode, MessagePack — integer encode, MessagePack — string encode, MessagePack — binary encode, MessagePack — array/map headers, MessagePack — decode_type, MessagePack — decode_str, MessagePack — integer round-trip.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b4eaa75f756c7639ecb2ad7b72a1f1ecd01b0c31e9bc7e7e1f31a2bc5f7f053`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b4eaa75f756c7639ecb2ad7b72a1f1ecd01b0c31e9bc7e7e1f31a2bc5f7f053`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b4eaa75f756c7639ecb2ad7b72a1f1ecd01b0c31e9bc7e7e1f31a2bc5f7f053`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/encoding/msgpack_spec.spl
mirror: doc/06_spec/unit/lib/common/encoding/msgpack_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/encoding/msgpack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/encoding/msgpack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/encoding/msgpack_spec.spl:278:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes to 1 byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/msgpack_spec.spl:283:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes to byte 0xC0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/msgpack_spec.spl:290:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'false encodes to 1 byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
