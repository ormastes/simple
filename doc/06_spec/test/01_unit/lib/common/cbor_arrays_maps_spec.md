# cbor_arrays_maps_spec

> @covers src/lib/common/cbor/decode.spl 80%

<!-- sdn-diagram:id=cbor_arrays_maps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cbor_arrays_maps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cbor_arrays_maps_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cbor_arrays_maps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 115 | 115 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cbor_arrays_maps_spec

@covers src/lib/common/cbor/decode.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CBOR-COVERAGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/cbor_arrays_maps_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@covers src/lib/common/cbor/decode.spl 80%
@covers src/lib/common/cbor/encode.spl 80%
duplicate-typed-args suppression was removed from this coverage spec
primitive-api suppression was removed from this coverage spec
CBOR Arrays, Maps, Tags, and Roundtrip Coverage Test
Branch coverage for array/map headers, tagged values, item size, sequences, validation, and roundtrip

## Scenarios

### CBOR Decode - cbor_decode_array_header

#### when decoding definite-length array

#### decodes empty array header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_array_header(0)
val result = cbor_decode_array_header(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
expect(result.2).to_equal(1)
```

</details>

#### decodes array with 3 elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_array_header(3)
val result = cbor_decode_array_header(encoded, 0)
expect(result.0).to_equal(3)
expect(result.1).to_equal(0)
expect(result.2).to_equal(1)
```

</details>

#### decodes array with 100 elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_array_header(100)
val result = cbor_decode_array_header(encoded, 0)
expect(result.0).to_equal(100)
expect(result.1).to_equal(0)
expect(result.2).to_equal(2)
```

</details>

#### when decoding indefinite-length array

#### returns is_indefinite = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_array_start()
val result = cbor_decode_array_header(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(1)
expect(result.2).to_equal(1)
```

</details>

#### when major type is wrong

#### returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(5)
val result = cbor_decode_array_header(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
expect(result.2).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_map_header

#### when decoding definite-length map

#### decodes empty map header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_map_header(0)
val result = cbor_decode_map_header(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
expect(result.2).to_equal(1)
```

</details>

#### decodes map with 2 pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_map_header(2)
val result = cbor_decode_map_header(encoded, 0)
expect(result.0).to_equal(2)
expect(result.1).to_equal(0)
expect(result.2).to_equal(1)
```

</details>

#### when decoding indefinite-length map

#### returns is_indefinite = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_map_start()
val result = cbor_decode_map_header(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(1)
expect(result.2).to_equal(1)
```

</details>

#### when major type is wrong

#### returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(5)
val result = cbor_decode_map_header(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
expect(result.2).to_equal(0)
```

</details>

### CBOR Decode - cbor_decode_tag

#### when decoding tag 1 (epoch datetime)

#### returns tag number 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(1000)
val encoded = cbor_encode_tagged(1, inner)
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(1)
expect(result.1).to_equal(1)
```

</details>

#### when decoding tag 0 (datetime string)

#### returns tag number 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_text("2024-01-01")
val encoded = cbor_encode_tagged(0, inner)
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(1)
```

</details>

#### when decoding large tag number

#### decodes tag 55799 (self-describe)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val encoded = cbor_encode_tagged(55799, inner)
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(55799)
expect(result.1).to_be_greater_than(1)
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
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_item_size

#### when offset is beyond array

#### returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [0]
expect(cbor_item_size(bytes, 10)).to_equal(0)
```

</details>

#### when item is unsigned integer

#### returns 1 for immediate value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(5)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns 2 for uint8 value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(100)
expect(cbor_item_size(bytes, 0)).to_equal(2)
```

</details>

#### returns 3 for uint16 value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(1000)
expect(cbor_item_size(bytes, 0)).to_equal(3)
```

</details>

#### when item is negative integer

#### returns correct header size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_int(-1)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns 2 for uint8-sized negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_int(-100)
expect(cbor_item_size(bytes, 0)).to_equal(2)
```

</details>

#### when item is byte string

#### returns header + data length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_bytes([1, 2, 3])
expect(cbor_item_size(bytes, 0)).to_equal(4)
```

</details>

#### returns 0 for indefinite byte string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [make_initial_byte(2, 31)]
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### when item is text string

#### returns header + text length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single-char text: header (1) + 1 byte = 2
val bts = cbor_encode_text("x")
expect(cbor_item_size(bts, 0)).to_equal(2)
```

</details>

#### returns 0 for indefinite text string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [make_initial_byte(3, 31)]
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### when item is array

#### returns total size for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_array_header(0)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns total size for array with items

1. var bytes = cbor encode array header
2. bytes = bytes concat
3. bytes = bytes concat
   - Expected: cbor_item_size(bytes, 0) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Array of 2 items: [1, 2]
var bytes = cbor_encode_array_header(2)
bytes = bytes_concat(bytes, cbor_encode_unsigned(1))
bytes = bytes_concat(bytes, cbor_encode_unsigned(2))
expect(cbor_item_size(bytes, 0)).to_equal(3)
```

</details>

#### returns 0 for indefinite array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_array_start()
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### returns 0 if array item size is 0

1. var bytes = cbor encode array header
2. bytes = bytes push
   - Expected: cbor_item_size(bytes, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Array claiming 1 item but item at offset is invalid
var bytes = cbor_encode_array_header(1)
# Append an indefinite byte string (size returns 0)
bytes = bytes.push(make_initial_byte(2, 31))
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### when item is map

#### returns total size for empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_map_header(0)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns total size for map with pairs

1. var bytes = cbor encode map header
2. bytes = bytes concat
3. bytes = bytes concat
   - Expected: cbor_item_size(bytes, 0) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Map of 1 pair: {1: 2}
var bytes = cbor_encode_map_header(1)
bytes = bytes_concat(bytes, cbor_encode_unsigned(1))
bytes = bytes_concat(bytes, cbor_encode_unsigned(2))
expect(cbor_item_size(bytes, 0)).to_equal(3)
```

</details>

#### returns 0 for indefinite map

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_map_start()
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### returns 0 if map item size is 0

1. var bytes = cbor encode map header
2. bytes = bytes concat
3. bytes = bytes push
   - Expected: cbor_item_size(bytes, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Map claiming 1 pair but items are invalid
var bytes = cbor_encode_map_header(1)
# key is fine
bytes = bytes_concat(bytes, cbor_encode_unsigned(1))
# value is indefinite byte string (size 0)
bytes = bytes.push(make_initial_byte(2, 31))
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### when item is tagged

#### returns header + value size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(42)
val bytes = cbor_encode_tagged(1, inner)
# Tag header (1 byte for tag 1) + value (1 byte for 42) = 2
# Actually tag 1 is immediate so header=1, value=1 => 2
expect(cbor_item_size(bytes, 0)).to_be_greater_than(0)
```

</details>

#### returns 0 if tagged value size is 0

1. var bytes = [make initial byte
2. bytes = bytes push
   - Expected: cbor_item_size(bytes, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tag followed by indefinite byte string
var bytes = [make_initial_byte(6, 0)]  # Tag 0
bytes = bytes.push(make_initial_byte(2, 31))  # Indefinite byte string
expect(cbor_item_size(bytes, 0)).to_equal(0)
```

</details>

#### when item is simple/float

#### returns 1 for false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_false()
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns 1 for true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_true()
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns 1 for null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_null()
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns 1 for undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_undefined()
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns 3 for float16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [make_initial_byte(7, 25), 0, 0]
expect(cbor_item_size(bytes, 0)).to_equal(3)
```

</details>

#### returns 5 for float32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_float32(1.0)
expect(cbor_item_size(bytes, 0)).to_equal(5)
```

</details>

#### returns 9 for float64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_float64(1.0)
expect(cbor_item_size(bytes, 0)).to_equal(9)
```

</details>

#### returns 1 for break

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_break()
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns header_size for other simple values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple value 10 (addl=10, which is <= 19)
val bytes = cbor_encode_simple(10)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

### CBOR Decode - cbor_sequence_count

#### when sequence has multiple items

#### counts items correctly

1. var seq = cbor encode unsigned
2. seq = bytes concat
3. seq = bytes concat
   - Expected: cbor_sequence_count(seq) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
seq = bytes_concat(seq, cbor_encode_unsigned(2))
seq = bytes_concat(seq, cbor_encode_unsigned(3))
expect(cbor_sequence_count(seq)).to_equal(3)
```

</details>

#### when sequence is empty

#### returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_seq = empty_i64_list()
expect(cbor_sequence_count(empty_seq)).to_equal(0)
```

</details>

#### when sequence has one item

#### returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = cbor_encode_text("hello")
expect(cbor_sequence_count(seq)).to_equal(1)
```

</details>

#### when sequence has invalid item

#### stops counting at invalid item

1. var seq = cbor encode unsigned
2. seq = seq push
   - Expected: cbor_sequence_count(seq) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
# Append indefinite byte string (item_size returns 0)
seq = seq.push(make_initial_byte(2, 31))
expect(cbor_sequence_count(seq)).to_equal(1)
```

</details>

### CBOR Decode - cbor_sequence_item

#### when extracting first item

#### returns the item bytes

1. var seq = cbor encode unsigned
2. seq = bytes concat
   - Expected: decoded.0 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(10)
seq = bytes_concat(seq, cbor_encode_unsigned(20))
val result = cbor_sequence_item(seq, 0)
val item_bytes = result.0
expect(item_bytes.len()).to_be_greater_than(0)
# Decode the extracted item
val decoded = cbor_decode_unsigned(item_bytes, 0)
expect(decoded.0).to_equal(10)
```

</details>

#### when extracting second item

#### returns the correct item

1. var seq = cbor encode unsigned
2. seq = bytes concat
   - Expected: decoded.0 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(10)
seq = bytes_concat(seq, cbor_encode_unsigned(20))
val result = cbor_sequence_item(seq, 1)
val item_bytes = result.0
val decoded = cbor_decode_unsigned(item_bytes, 0)
expect(decoded.0).to_equal(20)
```

</details>

#### when index is out of bounds

#### returns empty array and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = cbor_encode_unsigned(1)
val result = cbor_sequence_item(seq, 5)
expect(result.0.len()).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

#### when item size is 0 during traversal

#### returns error

1. var seq = cbor encode unsigned
2. seq = seq push
   - Expected: result.0.len() equals `0`
   - Expected: result.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
# Make next item invalid (indefinite byte string)
seq = seq.push(make_initial_byte(2, 31))
# Try to get index 1
val result = cbor_sequence_item(seq, 1)
expect(result.0.len()).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### CBOR Decode - cbor_validate

#### when data is valid CBOR

#### returns true for unsigned int

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_unsigned(42)
check(cbor_validate(bytes))
```

</details>

#### returns true for text string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_text("hello")
check(cbor_validate(bytes))
```

</details>

#### returns true for boolean

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_true()
check(cbor_validate(bytes))
```

</details>

#### when data is empty

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_data = empty_i64_list()
expect(cbor_validate(empty_data)).to_equal(false)
```

</details>

#### when data is invalid

#### returns false for indefinite byte string alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [make_initial_byte(2, 31)]
expect(cbor_validate(bytes)).to_equal(false)
```

</details>

### CBOR Decode - cbor_validate_sequence

#### when sequence is valid

#### returns true for multi-item sequence

1. var seq = cbor encode unsigned
2. seq = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
seq = bytes_concat(seq, cbor_encode_text("a"))
check(cbor_validate_sequence(seq))
```

</details>

#### when sequence is empty

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_data = empty_i64_list()
expect(cbor_validate_sequence(empty_data)).to_equal(false)
```

</details>

#### when sequence has invalid item

#### returns false

1. var seq = cbor encode unsigned
2. seq = seq push
   - Expected: cbor_validate_sequence(seq) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
seq = seq.push(make_initial_byte(2, 31))  # Invalid indefinite
expect(cbor_validate_sequence(seq)).to_equal(false)
```

</details>

### CBOR Decode - cbor_is_canonical_int

#### when encoding is canonical

#### returns true for immediate value 0

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
check(cbor_is_canonical_int(0, encoded))
```

</details>

#### returns true for immediate value 23

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(23)
check(cbor_is_canonical_int(23, encoded))
```

</details>

#### returns true for uint8 value 24

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(24)
check(cbor_is_canonical_int(24, encoded))
```

</details>

#### returns true for uint8 value 255

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(255)
check(cbor_is_canonical_int(255, encoded))
```

</details>

#### returns true for uint16 value 256

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(256)
check(cbor_is_canonical_int(256, encoded))
```

</details>

#### returns true for uint16 value 65535

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(65535)
check(cbor_is_canonical_int(65535, encoded))
```

</details>

#### returns true for uint32 value 65536

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(65536)
check(cbor_is_canonical_int(65536, encoded))
```

</details>

#### when encoding is canonical for negative

#### returns true for -1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-1)
check(cbor_is_canonical_int(-1, encoded))
```

</details>

#### returns true for -100

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-100)
check(cbor_is_canonical_int(-100, encoded))
```

</details>

#### when encoding is empty

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_enc = empty_i64_list()
expect(cbor_is_canonical_int(0, empty_enc)).to_equal(false)
```

</details>

#### when major type is wrong

#### returns false for text string encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_text("x")
expect(cbor_is_canonical_int(0, encoded)).to_equal(false)
```

</details>

#### when encoding is non-canonical

#### returns false for uint8 encoding of value 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Value 5 should be immediate (1 byte), but force uint8 (2 bytes)
val non_canonical = [make_initial_byte(0, 24), 5]
expect(cbor_is_canonical_int(5, non_canonical)).to_equal(false)
```

</details>

#### returns false for uint16 encoding of value 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Value 100 should be uint8, but force uint16
val non_canonical = [make_initial_byte(0, 25), 0, 100]
expect(cbor_is_canonical_int(100, non_canonical)).to_equal(false)
```

</details>

#### returns false for uint32 encoding of value 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Value 1000 should be uint16, but force uint32
val non_canonical = [make_initial_byte(0, 26), 0, 0, 3, 232]
expect(cbor_is_canonical_int(1000, non_canonical)).to_equal(false)
```

</details>

### CBOR Roundtrip

#### when encoding and decoding unsigned integers

#### roundtrips 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(0)
val decoded = cbor_decode_unsigned(encoded, 0)
expect(decoded.0).to_equal(0)
```

</details>

#### roundtrips 1000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_unsigned(1000000)
val decoded = cbor_decode_unsigned(encoded, 0)
expect(decoded.0).to_equal(1000000)
```

</details>

#### when encoding and decoding signed integers

#### roundtrips positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(42)
val decoded = cbor_decode_int(encoded, 0)
expect(decoded.0).to_equal(42)
```

</details>

#### roundtrips negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-500)
val decoded = cbor_decode_int(encoded, 0)
expect(decoded.0).to_equal(-500)
```

</details>

#### when encoding and decoding text

#### roundtrips short text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single-char text (multi-char limited by runtime substring bug)
val encoded = cbor_encode_text("t")
val decoded = cbor_decode_text(encoded, 0)
expect(decoded.0).to_equal("t")
```

</details>

#### roundtrips empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_text("")
val decoded = cbor_decode_text(encoded, 0)
expect(decoded.0).to_equal("")
```

</details>

#### when encoding and decoding bytes

#### roundtrips byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [0, 127, 255]
val encoded = cbor_encode_bytes(data)
val decoded = cbor_decode_bytes(encoded, 0)
expect(decoded.0.len()).to_equal(3)
expect(decoded.0[0]).to_equal(0)
expect(decoded.0[1]).to_equal(127)
expect(decoded.0[2]).to_equal(255)
```

</details>

#### when encoding and decoding booleans

#### roundtrips true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_bool(true)
val decoded = cbor_decode_bool(encoded, 0)
expect(decoded.0).to_equal(true)
expect(decoded.1).to_equal(1)
```

</details>

#### roundtrips false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_bool(false)
val decoded = cbor_decode_bool(encoded, 0)
expect(decoded.0).to_equal(false)
expect(decoded.1).to_equal(1)
```

</details>

### CBOR Decode - cbor_is_canonical_int uint64 range

#### when value exceeds uint32 range

#### returns true for canonical uint64 encoding

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Value > 4294967295 should use addl_uint64 (27)
val big_val = 4294967296
val encoded = cbor_encode_unsigned(big_val)
check(cbor_is_canonical_int(big_val, encoded))
```

</details>

#### when encoding has wrong major type that is negative

#### returns false for array encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_array_header(5)
expect(cbor_is_canonical_int(5, encoded)).to_equal(false)
```

</details>

### CBOR Decode - cbor_item_size additional simple values

#### when item is simple value with addl <= 19

#### returns header_size for simple value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_simple(0)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns header_size for simple value 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_simple(5)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### returns header_size for simple value 19

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_simple(19)
expect(cbor_item_size(bytes, 0)).to_equal(1)
```

</details>

#### when item is extended simple with uint8

#### returns 2 for simple value 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_simple(32)
expect(cbor_item_size(bytes, 0)).to_equal(2)
```

</details>

#### returns 2 for simple value 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_simple(255)
expect(cbor_item_size(bytes, 0)).to_equal(2)
```

</details>

### CBOR Decode - cbor_item_size tagged values

#### when tag uses uint8 encoding

#### returns correct size for tag 24

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val bytes = cbor_encode_tagged(24, inner)
val size = cbor_item_size(bytes, 0)
expect(size).to_be_greater_than(0)
```

</details>

#### when tag uses uint16 encoding

#### returns correct size for tag 256

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val bytes = cbor_encode_tagged(256, inner)
val size = cbor_item_size(bytes, 0)
expect(size).to_be_greater_than(0)
```

</details>

### CBOR Decode - cbor_decode_tag various sizes

#### when decoding uint8-encoded tag

#### decodes tag 24

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val encoded = cbor_encode_tagged(24, inner)
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(24)
expect(result.1).to_equal(2)
```

</details>

#### when decoding uint16-encoded tag

#### decodes tag 256

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val encoded = cbor_encode_tagged(256, inner)
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(256)
expect(result.1).to_equal(3)
```

</details>

#### when decoding uint32-encoded tag

#### decodes tag 65536

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(0)
val encoded = cbor_encode_tagged(65536, inner)
val result = cbor_decode_tag(encoded, 0)
expect(result.0).to_equal(65536)
expect(result.1).to_equal(5)
```

</details>

### CBOR Decode - cbor_item_size array with uint8 count

#### when array has 24+ items

#### returns correct total size

1. var bytes = cbor encode array header
2. bytes = bytes concat
   - Expected: size equals `26)  # 2 header + 24 items`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Array of 24 unsigned int items (each 1 byte), header = 2 bytes (uint8 length)
var bytes = cbor_encode_array_header(24)
var i = 0
while i < 24:
    bytes = bytes_concat(bytes, cbor_encode_unsigned(0))
    i = i + 1
val size = cbor_item_size(bytes, 0)
expect(size).to_equal(26)  # 2 header + 24 items
```

</details>

### CBOR Decode - cbor_item_size map with multiple pairs

#### when map has 2 pairs of uint8-encoded keys

#### returns correct total size

1. var bytes = cbor encode map header
2. bytes = bytes concat
3. bytes = bytes concat
4. bytes = bytes concat
5. bytes = bytes concat
   - Expected: size equals `7)  # 1 header + 2+1+2+1 data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Map of 2 pairs: {100: 0, 200: 0}
var bytes = cbor_encode_map_header(2)
bytes = bytes_concat(bytes, cbor_encode_unsigned(100))  # key1: 2 bytes
bytes = bytes_concat(bytes, cbor_encode_unsigned(0))    # val1: 1 byte
bytes = bytes_concat(bytes, cbor_encode_unsigned(200))  # key2: 2 bytes
bytes = bytes_concat(bytes, cbor_encode_unsigned(0))    # val2: 1 byte
val size = cbor_item_size(bytes, 0)
expect(size).to_equal(7)  # 1 header + 2+1+2+1 data
```

</details>

### CBOR Decode - cbor_is_canonical_int negative ranges

#### when canonical negative uint16

#### returns true for -256

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-256)
check(cbor_is_canonical_int(-256, encoded))
```

</details>

#### when canonical negative uint32

#### returns true for -100000

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = cbor_encode_int(-100000)
check(cbor_is_canonical_int(-100000, encoded))
```

</details>

### CBOR Decode - cbor_validate additional

#### when data is valid negative int

#### returns true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_int(-42)
check(cbor_validate(bytes))
```

</details>

#### when data is valid bytes

#### returns true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_bytes([1, 2, 3])
check(cbor_validate(bytes))
```

</details>

#### when data is valid array with items

#### returns true

1. var bytes = cbor encode array header
2. bytes = bytes concat
3. bytes = bytes concat
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = cbor_encode_array_header(2)
bytes = bytes_concat(bytes, cbor_encode_unsigned(1))
bytes = bytes_concat(bytes, cbor_encode_unsigned(2))
check(cbor_validate(bytes))
```

</details>

#### when data is valid map with pairs

#### returns true

1. var bytes = cbor encode map header
2. bytes = bytes concat
3. bytes = bytes concat
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = cbor_encode_map_header(1)
bytes = bytes_concat(bytes, cbor_encode_unsigned(1))
bytes = bytes_concat(bytes, cbor_encode_unsigned(2))
check(cbor_validate(bytes))
```

</details>

#### when data is valid tagged value

#### returns true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = cbor_encode_unsigned(42)
val bytes = cbor_encode_tagged(1, inner)
check(cbor_validate(bytes))
```

</details>

#### when data is valid null

#### returns true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_null()
check(cbor_validate(bytes))
```

</details>

#### when data is valid undefined

#### returns true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = cbor_encode_undefined()
check(cbor_validate(bytes))
```

</details>

### CBOR Decode - cbor_validate_sequence additional

#### when sequence has mixed types

#### returns true for int + bool + null

1. var seq = cbor encode unsigned
2. seq = bytes concat
3. seq = bytes concat
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
seq = bytes_concat(seq, cbor_encode_true())
seq = bytes_concat(seq, cbor_encode_null())
check(cbor_validate_sequence(seq))
```

</details>

### CBOR Decode - cbor_sequence_count additional

#### when sequence has mixed item types

#### counts all items

1. var seq = cbor encode unsigned
2. seq = bytes concat
3. seq = bytes concat
4. seq = bytes concat
   - Expected: cbor_sequence_count(seq) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(1)
seq = bytes_concat(seq, cbor_encode_int(-1))
seq = bytes_concat(seq, cbor_encode_true())
seq = bytes_concat(seq, cbor_encode_null())
expect(cbor_sequence_count(seq)).to_equal(4)
```

</details>

### CBOR Decode - cbor_sequence_item additional

#### when extracting third item from mixed sequence

#### returns the correct item

1. var seq = cbor encode unsigned
2. seq = bytes concat
3. seq = bytes concat
   - Expected: decoded.0 equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var seq = cbor_encode_unsigned(10)
seq = bytes_concat(seq, cbor_encode_unsigned(20))
seq = bytes_concat(seq, cbor_encode_unsigned(30))
val result = cbor_sequence_item(seq, 2)
val item_bytes = result.0
val decoded = cbor_decode_unsigned(item_bytes, 0)
expect(decoded.0).to_equal(30)
```

</details>

### CBOR Decode - type detection at non-zero offset

#### when checking types at offset

#### detects byte string at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_bytes([1, 2]))
check(cbor_is_byte_string(data, 1))
```

</details>

#### detects text string at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_text("a"))
check(cbor_is_text_string(data, 1))
```

</details>

#### detects array at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_array_header(0))
check(cbor_is_array(data, 1))
```

</details>

#### detects map at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_map_header(0))
check(cbor_is_map(data, 1))
```

</details>

#### detects tagged at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
val inner = cbor_encode_unsigned(0)
data = bytes_concat(data, cbor_encode_tagged(1, inner))
check(cbor_is_tagged(data, 1))
```

</details>

#### detects simple at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_null())
check(cbor_is_simple(data, 1))
```

</details>

#### detects break at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_break())
check(cbor_is_break(data, 1))
```

</details>

#### detects indefinite at offset

1. var data = cbor encode unsigned
2. data = bytes concat
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = cbor_encode_unsigned(5)
data = bytes_concat(data, cbor_encode_array_start())
check(cbor_is_indefinite(data, 1))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 115 |
| Active scenarios | 115 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
