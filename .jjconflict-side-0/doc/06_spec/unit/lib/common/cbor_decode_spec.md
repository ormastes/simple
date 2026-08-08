# cbor_decode_spec

> @covers src/lib/common/cbor/decode.spl 80%

<!-- sdn-diagram:id=cbor_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cbor_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cbor_decode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cbor_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 94 | 94 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cbor_decode_spec

@covers src/lib/common/cbor/decode.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CBOR-COVERAGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/unit/lib/common/cbor_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@covers src/lib/common/cbor/decode.spl 80%
duplicate-typed-args suppression was removed from this coverage spec
primitive-api suppression was removed from this coverage spec
CBOR Decode Coverage Test
Branch coverage for decode.spl: header parsing, type detection, int/string/bool/null decoding

## Scenarios

### CBOR Decode - decode_uint_value via cbor_decode_unsigned

#### when decoding immediate values (0..23)

#### decodes value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(1)
```

</details>

#### decodes value 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(23)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(23)
expect(result.1).to_equal(1)
```

</details>

#### decodes value 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(10)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(10)
expect(result.1).to_equal(1)
```

</details>

#### when decoding uint8 values (24..255)

#### decodes value 24

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(24)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(24)
expect(result.1).to_equal(2)
```

</details>

#### decodes value 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(255)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(255)
expect(result.1).to_equal(2)
```

</details>

#### when decoding uint16 values (256..65535)

#### decodes value 256

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(256)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(256)
expect(result.1).to_equal(3)
```

</details>

#### decodes value 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(1000)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(1000)
expect(result.1).to_equal(3)
```

</details>

#### decodes value 65535

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(65535)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(65535)
expect(result.1).to_equal(3)
```

</details>

#### when decoding uint32 values

#### decodes value 65536

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(65536)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(65536)
expect(result.1).to_equal(5)
```

</details>

#### decodes value 1000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(1000000)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(1000000)
expect(result.1).to_equal(5)
```

</details>

#### when bytes are truncated for uint8

#### returns error tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major type 0 + addl 24 (uint8 follows) but no second byte
val encoded = [make_initial_byte(0, 24)]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when bytes are truncated for uint16

#### returns error tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major type 0 + addl 25 (uint16 follows) but only 1 extra byte
val encoded = [make_initial_byte(0, 25), 0]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when bytes are truncated for uint32

#### returns error tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major type 0 + addl 26 (uint32 follows) but only 2 extra bytes
val encoded = [make_initial_byte(0, 26), 0, 0]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when bytes are truncated for uint64

#### returns error tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major type 0 + addl 27 (uint64 follows) but only 4 extra bytes
val encoded = [make_initial_byte(0, 27), 0, 0, 0, 0]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when major type is wrong

#### returns error for negative int bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Negative int initial byte
val encoded = [make_initial_byte(1, 5)]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_type

#### when offset is beyond array length

#### returns zero tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [0]
val result = cbor_decode_type(bytes, 5)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
expect(result.2).to_equal(0)
```

</details>

#### when decoding unsigned int header

#### returns major type 0 with correct header size for immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(5)
val result = cbor_decode_type(bytes, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(5)
expect(result.2).to_equal(1)
```

</details>

#### when decoding with addl_uint8

#### returns header_size 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(100)
val result = cbor_decode_type(bytes, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(24)
expect(result.2).to_equal(2)
```

</details>

#### when decoding with addl_uint16

#### returns header_size 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(500)
val result = cbor_decode_type(bytes, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(25)
expect(result.2).to_equal(3)
```

</details>

#### when decoding with addl_uint32

#### returns header_size 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(100000)
val result = cbor_decode_type(bytes, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(26)
expect(result.2).to_equal(5)
```

</details>

### CBOR Decode - cbor_is_unsigned_int

#### when byte is unsigned int

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(42)
check(cbor_is_unsigned_int(bytes, 0))
```

</details>

#### when byte is not unsigned int

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_int(-1)
expect(cbor_is_unsigned_int(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_negative_int

#### when byte is negative int

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_int(-1)
check(cbor_is_negative_int(bytes, 0))
```

</details>

#### when byte is not negative int

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_negative_int(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_byte_string

#### when byte is byte string

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_bytes([1, 2, 3])
check(cbor_is_byte_string(bytes, 0))
```

</details>

#### when byte is not byte string

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_byte_string(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_text_string

#### when byte is text string

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_text("hi")
check(cbor_is_text_string(bytes, 0))
```

</details>

#### when byte is not text string

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_text_string(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_array

#### when byte is array

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_array_header(3)
check(cbor_is_array(bytes, 0))
```

</details>

#### when byte is not array

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_array(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_map

#### when byte is map

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_map_header(2)
check(cbor_is_map(bytes, 0))
```

</details>

#### when byte is not map

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_map(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_tagged

#### when byte is tagged

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val bytes = cbor_encode_tagged(1, inner)
check(cbor_is_tagged(bytes, 0))
```

</details>

#### when byte is not tagged

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_tagged(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_simple

#### when byte is simple value

#### returns true for false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_false()
check(cbor_is_simple(bytes, 0))
```

</details>

#### returns true for null

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_null()
check(cbor_is_simple(bytes, 0))
```

</details>

#### when byte is not simple

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_simple(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_indefinite

#### when byte is indefinite-length array

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_array_start()
check(cbor_is_indefinite(bytes, 0))
```

</details>

#### when byte is definite-length

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_array_header(3)
expect(cbor_is_indefinite(bytes, 0)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_break

#### when byte is break code

#### returns true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_break()
check(cbor_is_break(bytes, 0))
```

</details>

#### when byte is not break

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(0)
expect(cbor_is_break(bytes, 0)).to_equal(false)
```

</details>

#### when offset is beyond array length

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [0xFF]
expect(cbor_is_break(bytes, 5)).to_equal(false)
```

</details>

### CBOR Decode - cbor_decode_int

#### when decoding positive integer

#### decodes as unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(42)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(42)
expect(result.1).to_be_greater_than(0)
```

</details>

#### when decoding negative integer

#### decodes -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-1)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(-1)
expect(result.1).to_equal(1)
```

</details>

#### decodes -100

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-100)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(-100)
expect(result.1).to_equal(2)
```

</details>

#### decodes -1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-1000)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(-1000)
expect(result.1).to_equal(3)
```

</details>

#### when decoding zero

#### returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(0)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(1)
```

</details>

#### when major type is wrong

#### returns error for text string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_text("abc")
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_bytes

#### when decoding definite-length byte string

#### decodes empty byte string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_bytes([])
val result = cbor_decode_bytes(encoded, 0)
expect(result.0.len()).to_equal(0)
expect(result.1).to_be_greater_than(0)
```

</details>

#### decodes short byte string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val encoded = cbor_encode_bytes(data)
val result = cbor_decode_bytes(encoded, 0)
expect(result.0.len()).to_equal(5)
expect(result.0[0]).to_equal(1)
expect(result.0[4]).to_equal(5)
```

</details>

#### when decoding indefinite-length byte string

#### decodes chunked byte string with break

- var encoded = [make initial byte
- encoded = bytes concat
- encoded = bytes concat
- encoded = encoded push
   - Expected: result.0.len() equals `3`
   - Expected: result.0[0] equals `10`
   - Expected: result.0[1] equals `20`
   - Expected: result.0[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build indefinite byte string: 0x5F [chunk1] [chunk2] 0xFF
var encoded = [make_initial_byte(2, 31)]
# Chunk 1: definite byte string [10, 20]
val chunk1 = cbor_encode_bytes([10, 20])
encoded = bytes_concat(encoded, chunk1)
# Chunk 2: definite byte string [30]
val chunk2 = cbor_encode_bytes([30])
encoded = bytes_concat(encoded, chunk2)
# Break code: 0xFF
encoded = encoded.push(0xFF)
val result = cbor_decode_bytes(encoded, 0)
expect(result.0.len()).to_equal(3)
expect(result.0[0]).to_equal(10)
expect(result.0[1]).to_equal(20)
expect(result.0[2]).to_equal(30)
expect(result.1).to_be_greater_than(0)
```

</details>

#### when major type is wrong

#### returns empty array and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(42)
val result = cbor_decode_bytes(encoded, 0)
expect(result.0.len()).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when bytes are truncated

#### returns error for too-short data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Byte string header claiming 10 bytes but only 2 available
val header = make_initial_byte(2, 24)  # Major 2 + addl 24 (uint8 follows)
val encoded = [header, 10, 0, 0]  # Claims 10 bytes, has only 2
val result = cbor_decode_bytes(encoded, 0)
expect(result.0.len()).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_text

#### when decoding definite-length text

#### decodes empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_text("")
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal("")
expect(result.1).to_be_greater_than(0)
```

</details>

#### decodes simple ASCII text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single-char text (multi-char limited by runtime substring bug)
val encoded = cbor_encode_text("h")
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal("h")
```

</details>

#### decodes text with space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_text(" ")
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal(" ")
```

</details>

#### when decoding indefinite-length text

#### decodes chunked text with break

- var encoded = [make initial byte
- encoded = bytes concat
- encoded = bytes concat
- encoded = encoded push
   - Expected: result.0 equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build indefinite text string: 0x7F [chunk1] [chunk2] 0xFF
var encoded = [make_initial_byte(3, 31)]
# Chunk 1: definite text "a"
val chunk1 = cbor_encode_text("a")
encoded = bytes_concat(encoded, chunk1)
# Chunk 2: definite text "b"
val chunk2 = cbor_encode_text("b")
encoded = bytes_concat(encoded, chunk2)
# Break code: 0xFF
encoded = encoded.push(0xFF)
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal("ab")
expect(result.1).to_be_greater_than(0)
```

</details>

#### when major type is wrong

#### returns empty text and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(42)
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal("")
expect(result.1).to_equal(0)
```

</details>

#### when text bytes are truncated

#### returns error for too-short data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Text string header claiming 10 bytes but only 2 available
val header = make_initial_byte(3, 24)  # Major 3 + addl 24 (uint8 follows)
val encoded = [header, 10, 65, 66]  # Claims 10 bytes, has only 2
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal("")
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_bool

#### when decoding false

#### returns false with 1 byte consumed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_false()
val result = cbor_decode_bool(encoded, 0)
expect(result.0).to_equal(false)
expect(result.1).to_equal(1)
```

</details>

#### when decoding true

#### returns true with 1 byte consumed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_true()
val result = cbor_decode_bool(encoded, 0)
expect(result.0).to_equal(true)
expect(result.1).to_equal(1)
```

</details>

#### when major type is wrong

#### returns false and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
val result = cbor_decode_bool(encoded, 0)
expect(result.0).to_equal(false)
expect(result.1).to_equal(0)
```

</details>

#### when simple value is not boolean

#### returns false and 0 for null

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_null()
val result = cbor_decode_bool(encoded, 0)
expect(result.0).to_equal(false)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_null

#### when decoding null

#### returns 1 with 1 byte consumed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_null()
val result = cbor_decode_null(encoded, 0)
expect(result.0).to_equal(1)
expect(result.1).to_equal(1)
```

</details>

#### when major type is wrong

#### returns 0 and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
val result = cbor_decode_null(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when simple value is not null

#### returns 0 and 0 for true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_true()
val result = cbor_decode_null(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_undefined

#### when decoding undefined

#### returns 1 with 1 byte consumed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_undefined()
val result = cbor_decode_undefined(encoded, 0)
expect(result.0).to_equal(1)
expect(result.1).to_equal(1)
```

</details>

#### when major type is wrong

#### returns 0 and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
val result = cbor_decode_undefined(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when simple value is not undefined

#### returns 0 and 0 for null

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_null()
val result = cbor_decode_undefined(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_simple_value

#### when decoding immediate simple value (0..19)

#### decodes value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_simple(0)
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(1)
```

</details>

#### decodes value 19

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_simple(19)
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(19)
expect(result.1).to_equal(1)
```

</details>

#### when decoding extended simple value (32..255)

#### decodes value 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_simple(32)
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(32)
expect(result.1).to_equal(2)
```

</details>

#### decodes value 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_simple(255)
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(255)
expect(result.1).to_equal(2)
```

</details>

#### when major type is wrong

#### returns 0 and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when truncated for uint8 extended simple

#### returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major 7, addl 24 (uint8) but no following byte
val encoded = [make_initial_byte(7, 24)]
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when addl is not immediate or uint8

#### returns 0 and 0 for boolean-range addl

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# simple_false = 20, simple_true = 21 are not <= 19 and not addl_uint8
val encoded = cbor_encode_false()
val result = cbor_decode_simple_value(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - non-zero offset

#### when multiple items are concatenated

#### decodes second item at correct offset

- var data = cbor encode unsigned
- data = bytes concat
   - Expected: result.0 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(10)
val second = cbor_encode_unsigned(20)
data = bytes_concat(data, second)
# First item is 1 byte (value 10), second starts at offset 1
val result = cbor_decode_unsigned(data, 1)
expect(result.0).to_equal(20)
```

</details>

#### decodes text after integer

- var data = cbor encode unsigned
- data = bytes concat
   - Expected: result.0 equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
val text_enc = cbor_encode_text("A")
data = bytes_concat(data, text_enc)
# Integer 5 is 1 byte, text starts at offset 1
val result = cbor_decode_text(data, 1)
expect(result.0).to_equal("A")
```

</details>

#### when offset points to boolean after int

#### decodes the boolean correctly

- var data = cbor encode unsigned
- data = bytes concat
   - Expected: result.0 is true
   - Expected: result.1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(100)
val bool_bytes = cbor_encode_true()
data = bytes_concat(data, bool_bytes)
# Int 100 uses 2 bytes (uint8), bool at offset 2
val result = cbor_decode_bool(data, 2)
expect(result.0).to_equal(true)
expect(result.1).to_equal(1)
```

</details>

### CBOR Decode - decode_uint_value reserved additional info

#### when additional info is reserved (28, 29, 30)

#### returns (0,0) for addl 28 via unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major 0 + addl 28 = 0*32+28 = 28
val encoded = [28]
val result = cbor_decode_unsigned(encoded, 0)
# addl=28 is not <=23, not 24,25,26,27 => falls through to (0,0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### returns (0,0) for addl 29 via unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = [29]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### returns (0,0) for addl 30 via unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = [30]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when additional info is indefinite (31) on integer

#### returns (0,0) for unsigned with addl 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major 0 + addl 31 = 31
val encoded = [31]
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_type uint64 header

#### when additional info is addl_uint64 (27)

#### returns header_size 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Major 0 + addl 27 = 27, need 8 payload bytes
val encoded = [27, 0, 0, 0, 0, 0, 0, 0, 1]
val result = cbor_decode_type(encoded, 0)
expect(result.0).to_equal(0)   # major_unsigned_int
expect(result.1).to_equal(27)  # addl_uint64
expect(result.2).to_equal(9)   # header_size
```

</details>

### CBOR Decode - cbor_decode_int wrong major types

#### when major type is byte string

#### returns (0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_bytes([1, 2])
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when major type is array

#### returns (0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_array_header(2)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when major type is map

#### returns (0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_map_header(1)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when major type is simple/float

#### returns (0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_true()
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - indefinite byte string error paths

#### when indefinite byte string has bad chunk

#### returns error when chunk decoding fails

- var encoded = [make initial byte
- encoded = encoded push
- encoded = encoded push
   - Expected: result.0.len() equals `0`
   - Expected: result.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Indefinite byte string header + a non-byte-string item + break
# 0x5F (indef byte string), then 0x01 (unsigned int 1, not a byte string chunk)
var encoded = [make_initial_byte(2, 31)]
# Put a non-byte-string as chunk - unsigned int, which will fail cbor_decode_bytes
encoded = encoded.push(1)  # unsigned int 1
encoded = encoded.push(0xFF)  # break
val result = cbor_decode_bytes(encoded, 0)
# The chunk decode should fail (major!=2), returning ([], 0)
expect(result.0.len()).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - indefinite text string error paths

#### when indefinite text string has bad chunk

#### returns error when chunk decoding fails

- var encoded = [make initial byte
- encoded = encoded push
- encoded = encoded push
   - Expected: result.0 equals ``
   - Expected: result.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Indefinite text string header + non-text-string item
var encoded = [make_initial_byte(3, 31)]
# Put a non-text-string as chunk - unsigned int 1
encoded = encoded.push(1)  # unsigned int 1
encoded = encoded.push(0xFF)  # break
val result = cbor_decode_text(encoded, 0)
expect(result.0).to_equal("")
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_unsigned uint64

#### when decoding uint64 value

#### decodes a large value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(4294967296)
val result = cbor_decode_unsigned(encoded, 0)
expect(result.0).to_equal(4294967296)
expect(result.1).to_equal(9)
```

</details>

### CBOR Decode - cbor_decode_bytes uint8-length

#### when decoding byte string with 24+ bytes

#### decodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a byte string with 25 bytes
var data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
val encoded = cbor_encode_bytes(data)
val result = cbor_decode_bytes(encoded, 0)
expect(result.0.len()).to_equal(25)
expect(result.0[0]).to_equal(1)
expect(result.0[24]).to_equal(25)
expect(result.1).to_be_greater_than(0)
```

</details>

### CBOR Decode - cbor_decode_int negative ranges

#### when decoding negative uint16-range

#### decodes -1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-1000)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(-1000)
```

</details>

#### when decoding negative uint32-range

#### decodes -100000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-100000)
val result = cbor_decode_int(encoded, 0)
expect(result.0).to_equal(-100000)
expect(result.1).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 94 |
| Active scenarios | 94 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
