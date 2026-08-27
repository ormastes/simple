# Cbor Types Specification

> Tests covering CBOR Types - byte_at, CBOR Types - bytes_append, CBOR Types - bytes_concat, CBOR Types - bytes_slice, CBOR Types - make_initial_byte, CBOR Types - get_major_type, CBOR Types - get_additional_info, CBOR Types - text_to_bytes, CBOR Types - bytes_to_text, CBOR Types - text_to_bytes extended chars, CBOR Types - bytes_to_text extended chars.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 73 | 73 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Types Specification

## Scenarios

### CBOR Types - byte_at

#### when index is valid

#### returns the byte at the given index

- returns the byte at the given index
   - Expected: byte_at(bytes, 0) equals `10`
   - Expected: byte_at(bytes, 1) equals `20`
   - Expected: byte_at(bytes, 2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the byte at the given index")
val bytes = [10, 20, 30]
expect(byte_at(bytes, 0)).to_equal(10)
expect(byte_at(bytes, 1)).to_equal(20)
expect(byte_at(bytes, 2)).to_equal(30)
```

</details>

#### when index is negative

#### returns 0

- returns 0
   - Expected: byte_at(bytes, -1) equals `0`
   - Expected: byte_at(bytes, -100) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0")
val bytes = [10, 20, 30]
expect(byte_at(bytes, -1)).to_equal(0)
expect(byte_at(bytes, -100)).to_equal(0)
```

</details>

#### when index is out of bounds

#### returns 0

- returns 0
   - Expected: byte_at(bytes, 3) equals `0`
   - Expected: byte_at(bytes, 100) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0")
val bytes = [10, 20, 30]
expect(byte_at(bytes, 3)).to_equal(0)
expect(byte_at(bytes, 100)).to_equal(0)
```

</details>

#### when array is empty

#### returns 0 for any index

- returns 0 for any index
   - Expected: byte_at(bts, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for any index")
val bts = empty_i64_list()
expect(byte_at(bts, 0)).to_equal(0)
```

</details>

### CBOR Types - bytes_append

#### when appending to array

#### returns array with new byte at end

- returns array with new byte at end
   - Expected: result.len() equals `3`
   - Expected: result[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns array with new byte at end")
val bytes = [1, 2]
val result = bytes_append(bytes, 3)
expect(result.len()).to_equal(3)
expect(result[2]).to_equal(3)
```

</details>

#### when appending to empty array

#### returns single-element array

- returns single-element array
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns single-element array")
val bts = empty_i64_list()
val result = bytes_append(bts, 42)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(42)
```

</details>

### CBOR Types - bytes_concat

#### when both arrays have elements

#### concatenates them

- concatenates them
   - Expected: result.len() equals `4`
   - Expected: result[0] equals `1`
   - Expected: result[3] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("concatenates them")
val a = [1, 2]
val b = [3, 4]
val result = bytes_concat(a, b)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(1)
expect(result[3]).to_equal(4)
```

</details>

#### when first array is empty

#### returns copy of second array

- returns copy of second array
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns copy of second array")
val empty = empty_i64_list()
val non_empty = [5, 6]
val result = bytes_concat(empty, non_empty)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(5)
```

</details>

#### when second array is empty

#### returns copy of first array

- returns copy of first array
   - Expected: result.len() equals `2`
   - Expected: result[1] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns copy of first array")
val non_empty = [7, 8]
val empty = empty_i64_list()
val result = bytes_concat(non_empty, empty)
expect(result.len()).to_equal(2)
expect(result[1]).to_equal(8)
```

</details>

### CBOR Types - bytes_slice

#### when slice is within bounds

#### extracts the correct slice

- extracts the correct slice
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `20`
   - Expected: result[1] equals `30`
   - Expected: result[2] equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the correct slice")
val bytes = [10, 20, 30, 40, 50]
val result = bytes_slice(bytes, 1, 3)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(20)
expect(result[1]).to_equal(30)
expect(result[2]).to_equal(40)
```

</details>

#### when slice extends past end

#### returns only available bytes

- returns only available bytes
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns only available bytes")
val bytes = [10, 20, 30]
val result = bytes_slice(bytes, 2, 5)
# Only index 2 is valid, rest are beyond end
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(30)
```

</details>

#### when start is at end

#### returns empty for zero-length

- returns empty for zero-length
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for zero-length")
val bytes = [10, 20]
val result = bytes_slice(bytes, 0, 0)
expect(result.len()).to_equal(0)
```

</details>

#### when start is negative

#### skips indexes before the buffer

- skips indexes before the buffer
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `10`
   - Expected: result[1] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips indexes before the buffer")
val bytes = [10, 20, 30]
val result = bytes_slice(bytes, -1, 3)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(10)
expect(result[1]).to_equal(20)
```

</details>

### CBOR Types - make_initial_byte

#### when encoding major type 0 with value 0

#### returns 0x00

- returns 0x00
   - Expected: make_initial_byte(0, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0x00")
expect(make_initial_byte(0, 0)).to_equal(0)
```

</details>

#### when encoding major type 0 with value 23

#### returns 23

- returns 23
   - Expected: make_initial_byte(0, 23) equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 23")
expect(make_initial_byte(0, 23)).to_equal(23)
```

</details>

#### when encoding major type 1 with value 0

#### returns 32

- returns 32
   - Expected: make_initial_byte(1, 0) equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 32")
# major_type 1 * 32 + 0 = 32
expect(make_initial_byte(1, 0)).to_equal(32)
```

</details>

#### when encoding major type 7 with value 31

#### returns 0xFF (255)

- returns 0xFF (255)
   - Expected: make_initial_byte(7, 31) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0xFF (255)")
# major_type 7 * 32 + 31 = 224 + 31 = 255
expect(make_initial_byte(7, 31)).to_equal(255)
```

</details>

#### when encoding all major types

#### correctly shifts major type bits

- correctly shifts major type bits
   - Expected: make_initial_byte(0, 0) equals `0`
   - Expected: make_initial_byte(1, 0) equals `32`
   - Expected: make_initial_byte(2, 0) equals `64`
   - Expected: make_initial_byte(3, 0) equals `96`
   - Expected: make_initial_byte(4, 0) equals `128`
   - Expected: make_initial_byte(5, 0) equals `160`
   - Expected: make_initial_byte(6, 0) equals `192`
   - Expected: make_initial_byte(7, 0) equals `224`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("correctly shifts major type bits")
expect(make_initial_byte(0, 0)).to_equal(0)
expect(make_initial_byte(1, 0)).to_equal(32)
expect(make_initial_byte(2, 0)).to_equal(64)
expect(make_initial_byte(3, 0)).to_equal(96)
expect(make_initial_byte(4, 0)).to_equal(128)
expect(make_initial_byte(5, 0)).to_equal(160)
expect(make_initial_byte(6, 0)).to_equal(192)
expect(make_initial_byte(7, 0)).to_equal(224)
```

</details>

### CBOR Types - get_major_type

#### when byte represents each major type

#### extracts the correct major type

- extracts the correct major type
   - Expected: get_major_type(0) equals `0`
   - Expected: get_major_type(32) equals `1`
   - Expected: get_major_type(64) equals `2`
   - Expected: get_major_type(96) equals `3`
   - Expected: get_major_type(128) equals `4`
   - Expected: get_major_type(160) equals `5`
   - Expected: get_major_type(192) equals `6`
   - Expected: get_major_type(224) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the correct major type")
expect(get_major_type(0)).to_equal(0)
expect(get_major_type(32)).to_equal(1)
expect(get_major_type(64)).to_equal(2)
expect(get_major_type(96)).to_equal(3)
expect(get_major_type(128)).to_equal(4)
expect(get_major_type(160)).to_equal(5)
expect(get_major_type(192)).to_equal(6)
expect(get_major_type(224)).to_equal(7)
```

</details>

#### when additional info is non-zero

#### still extracts correct major type

- still extracts correct major type
   - Expected: get_major_type(88) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still extracts correct major type")
# 0x58 = 88 = major 2 (byte string) + addl 24 (uint8)
expect(get_major_type(88)).to_equal(2)
```

</details>

### CBOR Types - get_additional_info

#### when extracting additional info

#### returns the low 5 bits

- returns the low 5 bits
   - Expected: get_additional_info(0) equals `0`
   - Expected: get_additional_info(23) equals `23`
   - Expected: get_additional_info(24) equals `24`
   - Expected: get_additional_info(31) equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the low 5 bits")
expect(get_additional_info(0)).to_equal(0)
expect(get_additional_info(23)).to_equal(23)
expect(get_additional_info(24)).to_equal(24)
expect(get_additional_info(31)).to_equal(31)
```

</details>

#### when major type is non-zero

#### still extracts correct additional info

- still extracts correct additional info
   - Expected: get_additional_info(56) equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still extracts correct additional info")
# 0x38 = 56 = major 1 (neg int) + addl 24 (uint8)
expect(get_additional_info(56)).to_equal(24)
```

</details>

### CBOR Types - text_to_bytes

#### when converting ASCII text

#### returns correct byte values for lowercase

- returns correct byte values for lowercase
   - Expected: result_a.len() equals `1`
   - Expected: result_a[0] equals `97`
   - Expected: result_b[0] equals `98`
   - Expected: result_c[0] equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct byte values for lowercase")
val result_a = text_to_bytes("a")
expect(result_a.len()).to_equal(1)
expect(result_a[0]).to_equal(97)
val result_b = text_to_bytes("b")
expect(result_b[0]).to_equal(98)
val result_c = text_to_bytes("c")
expect(result_c[0]).to_equal(99)
```

</details>

#### returns correct byte values for uppercase

- returns correct byte values for uppercase
   - Expected: result_a.len() equals `1`
   - Expected: result_a[0] equals `65`
   - Expected: result_b[0] equals `66`
   - Expected: result_c[0] equals `67`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct byte values for uppercase")
val result_a = text_to_bytes("A")
expect(result_a.len()).to_equal(1)
expect(result_a[0]).to_equal(65)
val result_b = text_to_bytes("B")
expect(result_b[0]).to_equal(66)
val result_c = text_to_bytes("C")
expect(result_c[0]).to_equal(67)
```

</details>

#### returns correct byte values for digits

- returns correct byte values for digits
   - Expected: result_0.len() equals `1`
   - Expected: result_0[0] equals `48`
   - Expected: result_1[0] equals `49`
   - Expected: result_2[0] equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct byte values for digits")
val result_0 = text_to_bytes("0")
expect(result_0.len()).to_equal(1)
expect(result_0[0]).to_equal(48)
val result_1 = text_to_bytes("1")
expect(result_1[0]).to_equal(49)
val result_2 = text_to_bytes("2")
expect(result_2[0]).to_equal(50)
```

</details>

#### returns correct value for space

- returns correct value for space
   - Expected: result[0] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct value for space")
val result = text_to_bytes(" ")
expect(result[0]).to_equal(32)
```

</details>

#### handles special characters

- handles special characters
   - Expected: result_bang[0] equals `33`
   - Expected: result_at[0] equals `64`
   - Expected: result_hash[0] equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles special characters")
val result_bang = text_to_bytes("!")
expect(result_bang[0]).to_equal(33)
val result_at = text_to_bytes("@")
expect(result_at[0]).to_equal(64)
val result_hash = text_to_bytes("#")
expect(result_hash[0]).to_equal(35)
```

</details>

#### when converting empty text

#### returns empty array

- returns empty array
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty array")
val result = text_to_bytes("")
expect(result.len()).to_equal(0)
```

</details>

#### when converting punctuation

#### handles braces and brackets

- handles braces and brackets
   - Expected: result_open[0] equals `123`
   - Expected: result_close[0] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles braces and brackets")
val result_open = text_to_bytes("{")
expect(result_open[0]).to_equal(123)
val result_close = text_to_bytes("}")
expect(result_close[0]).to_equal(125)
```

</details>

#### handles tilde and backtick

- handles tilde and backtick
   - Expected: result_tilde[0] equals `126`
   - Expected: result_backtick[0] equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles tilde and backtick")
val result_tilde = text_to_bytes("~")
expect(result_tilde[0]).to_equal(126)
val result_backtick = text_to_bytes("`")
expect(result_backtick[0]).to_equal(96)
```

</details>

### CBOR Types - bytes_to_text

#### when converting byte values to text

#### returns correct ASCII text for lowercase

- returns correct ASCII text for lowercase
   - Expected: result equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct ASCII text for lowercase")
val bytes = [104, 105]  # h, i
val result = cbor_bytes_to_text(bytes)
expect(result).to_equal("hi")
```

</details>

#### returns correct ASCII text for uppercase

- returns correct ASCII text for uppercase
   - Expected: result equals `HI`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct ASCII text for uppercase")
val bytes = [72, 73]  # H, I
val result = cbor_bytes_to_text(bytes)
expect(result).to_equal("HI")
```

</details>

#### returns correct text for digits

- returns correct text for digits
   - Expected: result equals `012`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns correct text for digits")
val bytes = [48, 49, 50]  # 0, 1, 2
val result = cbor_bytes_to_text(bytes)
expect(result).to_equal("012")
```

</details>

#### when converting empty byte array

#### returns empty text

- returns empty text
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty text")
val empty = empty_i64_list()
val result = cbor_bytes_to_text(empty)
expect(result).to_equal("")
```

</details>

#### when roundtripping

#### text_to_bytes then bytes_to_text returns original

- text_to_bytes then bytes_to_text returns original
   - Expected: roundtrip equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("text_to_bytes then bytes_to_text returns original")
# Single-char roundtrip (multi-char limited by runtime substring bug)
val original = "H"
val bts = text_to_bytes(original)
val roundtrip = cbor_bytes_to_text(bts)
expect(roundtrip).to_equal(original)
```

</details>

### CBOR Types - text_to_bytes extended chars

#### when converting additional lowercase letters

#### handles d through h

- handles d through h
   - Expected: text_to_bytes("d")[0] equals `100`
   - Expected: text_to_bytes("e")[0] equals `101`
   - Expected: text_to_bytes("f")[0] equals `102`
   - Expected: text_to_bytes("g")[0] equals `103`
   - Expected: text_to_bytes("h")[0] equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles d through h")
expect(text_to_bytes("d")[0]).to_equal(100)
expect(text_to_bytes("e")[0]).to_equal(101)
expect(text_to_bytes("f")[0]).to_equal(102)
expect(text_to_bytes("g")[0]).to_equal(103)
expect(text_to_bytes("h")[0]).to_equal(104)
```

</details>

#### handles i through m

- handles i through m
   - Expected: text_to_bytes("i")[0] equals `105`
   - Expected: text_to_bytes("j")[0] equals `106`
   - Expected: text_to_bytes("k")[0] equals `107`
   - Expected: text_to_bytes("l")[0] equals `108`
   - Expected: text_to_bytes("m")[0] equals `109`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles i through m")
expect(text_to_bytes("i")[0]).to_equal(105)
expect(text_to_bytes("j")[0]).to_equal(106)
expect(text_to_bytes("k")[0]).to_equal(107)
expect(text_to_bytes("l")[0]).to_equal(108)
expect(text_to_bytes("m")[0]).to_equal(109)
```

</details>

#### handles n through r

- handles n through r
   - Expected: text_to_bytes("n")[0] equals `110`
   - Expected: text_to_bytes("o")[0] equals `111`
   - Expected: text_to_bytes("p")[0] equals `112`
   - Expected: text_to_bytes("q")[0] equals `113`
   - Expected: text_to_bytes("r")[0] equals `114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles n through r")
expect(text_to_bytes("n")[0]).to_equal(110)
expect(text_to_bytes("o")[0]).to_equal(111)
expect(text_to_bytes("p")[0]).to_equal(112)
expect(text_to_bytes("q")[0]).to_equal(113)
expect(text_to_bytes("r")[0]).to_equal(114)
```

</details>

#### handles s through w

- handles s through w
   - Expected: text_to_bytes("s")[0] equals `115`
   - Expected: text_to_bytes("t")[0] equals `116`
   - Expected: text_to_bytes("u")[0] equals `117`
   - Expected: text_to_bytes("v")[0] equals `118`
   - Expected: text_to_bytes("w")[0] equals `119`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles s through w")
expect(text_to_bytes("s")[0]).to_equal(115)
expect(text_to_bytes("t")[0]).to_equal(116)
expect(text_to_bytes("u")[0]).to_equal(117)
expect(text_to_bytes("v")[0]).to_equal(118)
expect(text_to_bytes("w")[0]).to_equal(119)
```

</details>

#### handles x through z

- handles x through z
   - Expected: text_to_bytes("x")[0] equals `120`
   - Expected: text_to_bytes("y")[0] equals `121`
   - Expected: text_to_bytes("z")[0] equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles x through z")
expect(text_to_bytes("x")[0]).to_equal(120)
expect(text_to_bytes("y")[0]).to_equal(121)
expect(text_to_bytes("z")[0]).to_equal(122)
```

</details>

#### when converting additional uppercase letters

#### handles D through H

- handles D through H
   - Expected: text_to_bytes("D")[0] equals `68`
   - Expected: text_to_bytes("E")[0] equals `69`
   - Expected: text_to_bytes("F")[0] equals `70`
   - Expected: text_to_bytes("G")[0] equals `71`
   - Expected: text_to_bytes("H")[0] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles D through H")
expect(text_to_bytes("D")[0]).to_equal(68)
expect(text_to_bytes("E")[0]).to_equal(69)
expect(text_to_bytes("F")[0]).to_equal(70)
expect(text_to_bytes("G")[0]).to_equal(71)
expect(text_to_bytes("H")[0]).to_equal(72)
```

</details>

#### handles I through M

- handles I through M
   - Expected: text_to_bytes("I")[0] equals `73`
   - Expected: text_to_bytes("J")[0] equals `74`
   - Expected: text_to_bytes("K")[0] equals `75`
   - Expected: text_to_bytes("L")[0] equals `76`
   - Expected: text_to_bytes("M")[0] equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles I through M")
expect(text_to_bytes("I")[0]).to_equal(73)
expect(text_to_bytes("J")[0]).to_equal(74)
expect(text_to_bytes("K")[0]).to_equal(75)
expect(text_to_bytes("L")[0]).to_equal(76)
expect(text_to_bytes("M")[0]).to_equal(77)
```

</details>

#### handles N through R

- handles N through R
   - Expected: text_to_bytes("N")[0] equals `78`
   - Expected: text_to_bytes("O")[0] equals `79`
   - Expected: text_to_bytes("P")[0] equals `80`
   - Expected: text_to_bytes("Q")[0] equals `81`
   - Expected: text_to_bytes("R")[0] equals `82`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles N through R")
expect(text_to_bytes("N")[0]).to_equal(78)
expect(text_to_bytes("O")[0]).to_equal(79)
expect(text_to_bytes("P")[0]).to_equal(80)
expect(text_to_bytes("Q")[0]).to_equal(81)
expect(text_to_bytes("R")[0]).to_equal(82)
```

</details>

#### handles S through W

- handles S through W
   - Expected: text_to_bytes("S")[0] equals `83`
   - Expected: text_to_bytes("T")[0] equals `84`
   - Expected: text_to_bytes("U")[0] equals `85`
   - Expected: text_to_bytes("V")[0] equals `86`
   - Expected: text_to_bytes("W")[0] equals `87`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles S through W")
expect(text_to_bytes("S")[0]).to_equal(83)
expect(text_to_bytes("T")[0]).to_equal(84)
expect(text_to_bytes("U")[0]).to_equal(85)
expect(text_to_bytes("V")[0]).to_equal(86)
expect(text_to_bytes("W")[0]).to_equal(87)
```

</details>

#### handles X through Z

- handles X through Z
   - Expected: text_to_bytes("X")[0] equals `88`
   - Expected: text_to_bytes("Y")[0] equals `89`
   - Expected: text_to_bytes("Z")[0] equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles X through Z")
expect(text_to_bytes("X")[0]).to_equal(88)
expect(text_to_bytes("Y")[0]).to_equal(89)
expect(text_to_bytes("Z")[0]).to_equal(90)
```

</details>

#### when converting digits

#### handles 3 through 9

- handles 3 through 9
   - Expected: text_to_bytes("3")[0] equals `51`
   - Expected: text_to_bytes("4")[0] equals `52`
   - Expected: text_to_bytes("5")[0] equals `53`
   - Expected: text_to_bytes("6")[0] equals `54`
   - Expected: text_to_bytes("7")[0] equals `55`
   - Expected: text_to_bytes("8")[0] equals `56`
   - Expected: text_to_bytes("9")[0] equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles 3 through 9")
expect(text_to_bytes("3")[0]).to_equal(51)
expect(text_to_bytes("4")[0]).to_equal(52)
expect(text_to_bytes("5")[0]).to_equal(53)
expect(text_to_bytes("6")[0]).to_equal(54)
expect(text_to_bytes("7")[0]).to_equal(55)
expect(text_to_bytes("8")[0]).to_equal(56)
expect(text_to_bytes("9")[0]).to_equal(57)
```

</details>

#### when converting special characters

#### handles quote and dollar and percent

- handles quote and dollar and percent
   - Expected: text_to_bytes("\"")[0] equals `34`
   - Expected: text_to_bytes("$")[0] equals `36`
   - Expected: text_to_bytes("%")[0] equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles quote and dollar and percent")
expect(text_to_bytes("\"")[0]).to_equal(34)
expect(text_to_bytes("$")[0]).to_equal(36)
expect(text_to_bytes("%")[0]).to_equal(37)
```

</details>

#### handles ampersand and apostrophe

- handles ampersand and apostrophe
   - Expected: text_to_bytes("&")[0] equals `38`
   - Expected: text_to_bytes("'")[0] equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles ampersand and apostrophe")
expect(text_to_bytes("&")[0]).to_equal(38)
expect(text_to_bytes("'")[0]).to_equal(39)
```

</details>

#### handles parentheses and asterisk

- handles parentheses and asterisk
   - Expected: text_to_bytes("(")[0] equals `40`
   - Expected: text_to_bytes(")")[0] equals `41`
   - Expected: text_to_bytes("*")[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles parentheses and asterisk")
expect(text_to_bytes("(")[0]).to_equal(40)
expect(text_to_bytes(")")[0]).to_equal(41)
expect(text_to_bytes("*")[0]).to_equal(42)
```

</details>

#### handles plus comma minus period

- handles plus comma minus period
   - Expected: text_to_bytes("+")[0] equals `43`
   - Expected: text_to_bytes(",")[0] equals `44`
   - Expected: text_to_bytes("-")[0] equals `45`
   - Expected: text_to_bytes(".")[0] equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles plus comma minus period")
expect(text_to_bytes("+")[0]).to_equal(43)
expect(text_to_bytes(",")[0]).to_equal(44)
expect(text_to_bytes("-")[0]).to_equal(45)
expect(text_to_bytes(".")[0]).to_equal(46)
```

</details>

#### handles slash colon semicolon

- handles slash colon semicolon
   - Expected: text_to_bytes("/")[0] equals `47`
   - Expected: text_to_bytes(":")[0] equals `58`
   - Expected: text_to_bytes(";")[0] equals `59`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles slash colon semicolon")
expect(text_to_bytes("/")[0]).to_equal(47)
expect(text_to_bytes(":")[0]).to_equal(58)
expect(text_to_bytes(";")[0]).to_equal(59)
```

</details>

#### handles angle brackets equals question

- handles angle brackets equals question
   - Expected: text_to_bytes("<")[0] equals `60`
   - Expected: text_to_bytes("=")[0] equals `61`
   - Expected: text_to_bytes(">")[0] equals `62`
   - Expected: text_to_bytes("?")[0] equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles angle brackets equals question")
expect(text_to_bytes("<")[0]).to_equal(60)
expect(text_to_bytes("=")[0]).to_equal(61)
expect(text_to_bytes(">")[0]).to_equal(62)
expect(text_to_bytes("?")[0]).to_equal(63)
```

</details>

#### handles brackets backslash caret underscore

- handles brackets backslash caret underscore
   - Expected: text_to_bytes("[")[0] equals `91`
   - Expected: text_to_bytes("\\")[0] equals `92`
   - Expected: text_to_bytes("]")[0] equals `93`
   - Expected: text_to_bytes("^")[0] equals `94`
   - Expected: text_to_bytes("_")[0] equals `95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles brackets backslash caret underscore")
expect(text_to_bytes("[")[0]).to_equal(91)
expect(text_to_bytes("\\")[0]).to_equal(92)
expect(text_to_bytes("]")[0]).to_equal(93)
expect(text_to_bytes("^")[0]).to_equal(94)
expect(text_to_bytes("_")[0]).to_equal(95)
```

</details>

#### handles pipe

- handles pipe
   - Expected: text_to_bytes("|")[0] equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles pipe")
expect(text_to_bytes("|")[0]).to_equal(124)
```

</details>

### CBOR Types - bytes_to_text extended chars

#### when converting additional lowercase byte values

#### handles d through h

- handles d through h
   - Expected: cbor_bytes_to_text([100]) equals `d`
   - Expected: cbor_bytes_to_text([101]) equals `e`
   - Expected: cbor_bytes_to_text([102]) equals `f`
   - Expected: cbor_bytes_to_text([103]) equals `g`
   - Expected: cbor_bytes_to_text([104]) equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles d through h")
expect(cbor_bytes_to_text([100])).to_equal("d")
expect(cbor_bytes_to_text([101])).to_equal("e")
expect(cbor_bytes_to_text([102])).to_equal("f")
expect(cbor_bytes_to_text([103])).to_equal("g")
expect(cbor_bytes_to_text([104])).to_equal("h")
```

</details>

#### handles i through m

- handles i through m
   - Expected: cbor_bytes_to_text([105]) equals `i`
   - Expected: cbor_bytes_to_text([106]) equals `j`
   - Expected: cbor_bytes_to_text([107]) equals `k`
   - Expected: cbor_bytes_to_text([108]) equals `l`
   - Expected: cbor_bytes_to_text([109]) equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles i through m")
expect(cbor_bytes_to_text([105])).to_equal("i")
expect(cbor_bytes_to_text([106])).to_equal("j")
expect(cbor_bytes_to_text([107])).to_equal("k")
expect(cbor_bytes_to_text([108])).to_equal("l")
expect(cbor_bytes_to_text([109])).to_equal("m")
```

</details>

#### handles n through r

- handles n through r
   - Expected: cbor_bytes_to_text([110]) equals `n`
   - Expected: cbor_bytes_to_text([111]) equals `o`
   - Expected: cbor_bytes_to_text([112]) equals `p`
   - Expected: cbor_bytes_to_text([113]) equals `q`
   - Expected: cbor_bytes_to_text([114]) equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles n through r")
expect(cbor_bytes_to_text([110])).to_equal("n")
expect(cbor_bytes_to_text([111])).to_equal("o")
expect(cbor_bytes_to_text([112])).to_equal("p")
expect(cbor_bytes_to_text([113])).to_equal("q")
expect(cbor_bytes_to_text([114])).to_equal("r")
```

</details>

#### handles s through w

- handles s through w
   - Expected: cbor_bytes_to_text([115]) equals `s`
   - Expected: cbor_bytes_to_text([116]) equals `t`
   - Expected: cbor_bytes_to_text([117]) equals `u`
   - Expected: cbor_bytes_to_text([118]) equals `v`
   - Expected: cbor_bytes_to_text([119]) equals `w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles s through w")
expect(cbor_bytes_to_text([115])).to_equal("s")
expect(cbor_bytes_to_text([116])).to_equal("t")
expect(cbor_bytes_to_text([117])).to_equal("u")
expect(cbor_bytes_to_text([118])).to_equal("v")
expect(cbor_bytes_to_text([119])).to_equal("w")
```

</details>

#### handles x through z

- handles x through z
   - Expected: cbor_bytes_to_text([120]) equals `x`
   - Expected: cbor_bytes_to_text([121]) equals `y`
   - Expected: cbor_bytes_to_text([122]) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles x through z")
expect(cbor_bytes_to_text([120])).to_equal("x")
expect(cbor_bytes_to_text([121])).to_equal("y")
expect(cbor_bytes_to_text([122])).to_equal("z")
```

</details>

#### when converting additional uppercase byte values

#### handles D through H

- handles D through H
   - Expected: cbor_bytes_to_text([68]) equals `D`
   - Expected: cbor_bytes_to_text([69]) equals `E`
   - Expected: cbor_bytes_to_text([70]) equals `F`
   - Expected: cbor_bytes_to_text([71]) equals `G`
   - Expected: cbor_bytes_to_text([72]) equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles D through H")
expect(cbor_bytes_to_text([68])).to_equal("D")
expect(cbor_bytes_to_text([69])).to_equal("E")
expect(cbor_bytes_to_text([70])).to_equal("F")
expect(cbor_bytes_to_text([71])).to_equal("G")
expect(cbor_bytes_to_text([72])).to_equal("H")
```

</details>

#### handles I through M

- handles I through M
   - Expected: cbor_bytes_to_text([73]) equals `I`
   - Expected: cbor_bytes_to_text([74]) equals `J`
   - Expected: cbor_bytes_to_text([75]) equals `K`
   - Expected: cbor_bytes_to_text([76]) equals `L`
   - Expected: cbor_bytes_to_text([77]) equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles I through M")
expect(cbor_bytes_to_text([73])).to_equal("I")
expect(cbor_bytes_to_text([74])).to_equal("J")
expect(cbor_bytes_to_text([75])).to_equal("K")
expect(cbor_bytes_to_text([76])).to_equal("L")
expect(cbor_bytes_to_text([77])).to_equal("M")
```

</details>

#### handles N through R

- handles N through R
   - Expected: cbor_bytes_to_text([78]) equals `N`
   - Expected: cbor_bytes_to_text([79]) equals `O`
   - Expected: cbor_bytes_to_text([80]) equals `P`
   - Expected: cbor_bytes_to_text([81]) equals `Q`
   - Expected: cbor_bytes_to_text([82]) equals `R`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles N through R")
expect(cbor_bytes_to_text([78])).to_equal("N")
expect(cbor_bytes_to_text([79])).to_equal("O")
expect(cbor_bytes_to_text([80])).to_equal("P")
expect(cbor_bytes_to_text([81])).to_equal("Q")
expect(cbor_bytes_to_text([82])).to_equal("R")
```

</details>

#### handles S through W

- handles S through W
   - Expected: cbor_bytes_to_text([83]) equals `S`
   - Expected: cbor_bytes_to_text([84]) equals `T`
   - Expected: cbor_bytes_to_text([85]) equals `U`
   - Expected: cbor_bytes_to_text([86]) equals `V`
   - Expected: cbor_bytes_to_text([87]) equals `W`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles S through W")
expect(cbor_bytes_to_text([83])).to_equal("S")
expect(cbor_bytes_to_text([84])).to_equal("T")
expect(cbor_bytes_to_text([85])).to_equal("U")
expect(cbor_bytes_to_text([86])).to_equal("V")
expect(cbor_bytes_to_text([87])).to_equal("W")
```

</details>

#### handles X through Z

- handles X through Z
   - Expected: cbor_bytes_to_text([88]) equals `X`
   - Expected: cbor_bytes_to_text([89]) equals `Y`
   - Expected: cbor_bytes_to_text([90]) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles X through Z")
expect(cbor_bytes_to_text([88])).to_equal("X")
expect(cbor_bytes_to_text([89])).to_equal("Y")
expect(cbor_bytes_to_text([90])).to_equal("Z")
```

</details>

#### when converting digit byte values

#### handles 3 through 9

- handles 3 through 9
   - Expected: cbor_bytes_to_text([51]) equals `3`
   - Expected: cbor_bytes_to_text([52]) equals `4`
   - Expected: cbor_bytes_to_text([53]) equals `5`
   - Expected: cbor_bytes_to_text([54]) equals `6`
   - Expected: cbor_bytes_to_text([55]) equals `7`
   - Expected: cbor_bytes_to_text([56]) equals `8`
   - Expected: cbor_bytes_to_text([57]) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles 3 through 9")
expect(cbor_bytes_to_text([51])).to_equal("3")
expect(cbor_bytes_to_text([52])).to_equal("4")
expect(cbor_bytes_to_text([53])).to_equal("5")
expect(cbor_bytes_to_text([54])).to_equal("6")
expect(cbor_bytes_to_text([55])).to_equal("7")
expect(cbor_bytes_to_text([56])).to_equal("8")
expect(cbor_bytes_to_text([57])).to_equal("9")
```

</details>

#### when converting special character byte values

#### handles quote dollar percent

- handles quote dollar percent
   - Expected: cbor_bytes_to_text([34]) equals `"`
   - Expected: cbor_bytes_to_text([36]) equals `$`
   - Expected: cbor_bytes_to_text([37]) equals `%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles quote dollar percent")
expect(cbor_bytes_to_text([34])).to_equal("\"")
expect(cbor_bytes_to_text([36])).to_equal("$")
expect(cbor_bytes_to_text([37])).to_equal("%")
```

</details>

#### handles ampersand apostrophe

- handles ampersand apostrophe
   - Expected: cbor_bytes_to_text([38]) equals `&`
   - Expected: cbor_bytes_to_text([39]) equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles ampersand apostrophe")
expect(cbor_bytes_to_text([38])).to_equal("&")
expect(cbor_bytes_to_text([39])).to_equal("'")
```

</details>

#### handles parentheses asterisk

- handles parentheses asterisk
   - Expected: cbor_bytes_to_text([40]) equals `(`
   - Expected: cbor_bytes_to_text([41]) equals `)`
   - Expected: cbor_bytes_to_text([42]) equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles parentheses asterisk")
expect(cbor_bytes_to_text([40])).to_equal("(")
expect(cbor_bytes_to_text([41])).to_equal(")")
expect(cbor_bytes_to_text([42])).to_equal("*")
```

</details>

#### handles plus comma minus period

- handles plus comma minus period
   - Expected: cbor_bytes_to_text([43]) equals `+`
   - Expected: cbor_bytes_to_text([44]) equals `,`
   - Expected: cbor_bytes_to_text([45]) equals `-`
   - Expected: cbor_bytes_to_text([46]) equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles plus comma minus period")
expect(cbor_bytes_to_text([43])).to_equal("+")
expect(cbor_bytes_to_text([44])).to_equal(",")
expect(cbor_bytes_to_text([45])).to_equal("-")
expect(cbor_bytes_to_text([46])).to_equal(".")
```

</details>

#### handles slash colon semicolon

- handles slash colon semicolon
   - Expected: cbor_bytes_to_text([47]) equals `/`
   - Expected: cbor_bytes_to_text([58]) equals `:`
   - Expected: cbor_bytes_to_text([59]) equals `;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles slash colon semicolon")
expect(cbor_bytes_to_text([47])).to_equal("/")
expect(cbor_bytes_to_text([58])).to_equal(":")
expect(cbor_bytes_to_text([59])).to_equal(";")
```

</details>

#### handles angle brackets equals question

- handles angle brackets equals question
   - Expected: cbor_bytes_to_text([60]) equals `<`
   - Expected: cbor_bytes_to_text([61]) equals `=`
   - Expected: cbor_bytes_to_text([62]) equals `>`
   - Expected: cbor_bytes_to_text([63]) equals `?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles angle brackets equals question")
expect(cbor_bytes_to_text([60])).to_equal("<")
expect(cbor_bytes_to_text([61])).to_equal("=")
expect(cbor_bytes_to_text([62])).to_equal(">")
expect(cbor_bytes_to_text([63])).to_equal("?")
```

</details>

#### handles brackets backslash caret underscore

- handles brackets backslash caret underscore
   - Expected: cbor_bytes_to_text([91]) equals `[`
   - Expected: cbor_bytes_to_text([92]) equals `\\`
   - Expected: cbor_bytes_to_text([93]) equals `]`
   - Expected: cbor_bytes_to_text([94]) equals `^`
   - Expected: cbor_bytes_to_text([95]) equals `_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles brackets backslash caret underscore")
expect(cbor_bytes_to_text([91])).to_equal("[")
expect(cbor_bytes_to_text([92])).to_equal("\\")
expect(cbor_bytes_to_text([93])).to_equal("]")
expect(cbor_bytes_to_text([94])).to_equal("^")
expect(cbor_bytes_to_text([95])).to_equal("_")
```

</details>

#### handles pipe

- handles pipe
   - Expected: cbor_bytes_to_text([124]) equals `|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles pipe")
expect(cbor_bytes_to_text([124])).to_equal("|")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR Types - byte_at, CBOR Types - bytes_append, CBOR Types - bytes_concat, CBOR Types - bytes_slice, CBOR Types - make_initial_byte, CBOR Types - get_major_type, CBOR Types - get_additional_info, CBOR Types - text_to_bytes, CBOR Types - bytes_to_text, CBOR Types - text_to_bytes extended chars, CBOR Types - bytes_to_text extended chars.
- CBOR Types - byte_at
- CBOR Types - bytes_append
- CBOR Types - bytes_concat
- CBOR Types - bytes_slice
- CBOR Types - make_initial_byte
- CBOR Types - get_major_type
- CBOR Types - get_additional_info
- CBOR Types - text_to_bytes
- CBOR Types - bytes_to_text
- CBOR Types - text_to_bytes extended chars
- CBOR Types - bytes_to_text extended chars

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 73 |
| Active scenarios | 73 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb961eef84720238c9123d121d0d3cf63e7dca7f64786566ac697bcad5e10789`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb961eef84720238c9123d121d0d3cf63e7dca7f64786566ac697bcad5e10789`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb961eef84720238c9123d121d0d3cf63e7dca7f64786566ac697bcad5e10789`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/cbor_types_spec.spl
mirror: doc/06_spec/01_unit/lib/common/cbor_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/cbor_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/cbor_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/cbor_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 154 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/cbor_types_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the byte at the given index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_types_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_types_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
