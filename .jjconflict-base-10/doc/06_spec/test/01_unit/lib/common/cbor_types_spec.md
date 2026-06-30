# cbor_types_spec

> @covers src/lib/common/cbor/types.spl 80%

<!-- sdn-diagram:id=cbor_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cbor_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cbor_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cbor_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 73 | 73 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cbor_types_spec

@covers src/lib/common/cbor/types.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CBOR-COVERAGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/cbor_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@covers src/lib/common/cbor/types.spl 80%
duplicate-typed-args suppression was removed from this coverage spec
primitive-api suppression was removed from this coverage spec
CBOR Types Coverage Test
Branch coverage for types.spl: byte array helpers + text/byte conversion

## Scenarios

### CBOR Types - byte_at

#### when index is valid

#### returns the byte at the given index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [10, 20, 30]
expect(byte_at(bytes, 0)).to_equal(10)
expect(byte_at(bytes, 1)).to_equal(20)
expect(byte_at(bytes, 2)).to_equal(30)
```

</details>

#### when index is negative

#### returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [10, 20, 30]
expect(byte_at(bytes, -1)).to_equal(0)
expect(byte_at(bytes, -100)).to_equal(0)
```

</details>

#### when index is out of bounds

#### returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [10, 20, 30]
expect(byte_at(bytes, 3)).to_equal(0)
expect(byte_at(bytes, 100)).to_equal(0)
```

</details>

#### when array is empty

#### returns 0 for any index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bts = empty_i64_list()
expect(byte_at(bts, 0)).to_equal(0)
```

</details>

### CBOR Types - bytes_append

#### when appending to array

#### returns array with new byte at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [1, 2]
val result = bytes_append(bytes, 3)
expect(result.len()).to_equal(3)
expect(result[2]).to_equal(3)
```

</details>

#### when appending to empty array

#### returns single-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bts = empty_i64_list()
val result = bytes_append(bts, 42)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(42)
```

</details>

### CBOR Types - bytes_concat

#### when both arrays have elements

#### concatenates them

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = empty_i64_list()
val non_empty = [5, 6]
val result = bytes_concat(empty, non_empty)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(5)
```

</details>

#### when second array is empty

#### returns copy of first array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [10, 20, 30]
val result = bytes_slice(bytes, 2, 5)
# Only index 2 is valid, rest are beyond end
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(30)
```

</details>

#### when start is at end

#### returns empty for zero-length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [10, 20]
val result = bytes_slice(bytes, 0, 0)
expect(result.len()).to_equal(0)
```

</details>

#### when start is negative

#### skips indexes before the buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(make_initial_byte(0, 0)).to_equal(0)
```

</details>

#### when encoding major type 0 with value 23

#### returns 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(make_initial_byte(0, 23)).to_equal(23)
```

</details>

#### when encoding major type 1 with value 0

#### returns 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# major_type 1 * 32 + 0 = 32
expect(make_initial_byte(1, 0)).to_equal(32)
```

</details>

#### when encoding major type 7 with value 31

#### returns 0xFF (255)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# major_type 7 * 32 + 31 = 224 + 31 = 255
expect(make_initial_byte(7, 31)).to_equal(255)
```

</details>

#### when encoding all major types

#### correctly shifts major type bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x58 = 88 = major 2 (byte string) + addl 24 (uint8)
expect(get_major_type(88)).to_equal(2)
```

</details>

### CBOR Types - get_additional_info

#### when extracting additional info

#### returns the low 5 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_additional_info(0)).to_equal(0)
expect(get_additional_info(23)).to_equal(23)
expect(get_additional_info(24)).to_equal(24)
expect(get_additional_info(31)).to_equal(31)
```

</details>

#### when major type is non-zero

#### still extracts correct additional info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x38 = 56 = major 1 (neg int) + addl 24 (uint8)
expect(get_additional_info(56)).to_equal(24)
```

</details>

### CBOR Types - text_to_bytes

#### when converting ASCII text

#### returns correct byte values for lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_to_bytes(" ")
expect(result[0]).to_equal(32)
```

</details>

#### handles special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_to_bytes("")
expect(result.len()).to_equal(0)
```

</details>

#### when converting punctuation

#### handles braces and brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result_open = text_to_bytes("{")
expect(result_open[0]).to_equal(123)
val result_close = text_to_bytes("}")
expect(result_close[0]).to_equal(125)
```

</details>

#### handles tilde and backtick

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result_tilde = text_to_bytes("~")
expect(result_tilde[0]).to_equal(126)
val result_backtick = text_to_bytes("`")
expect(result_backtick[0]).to_equal(96)
```

</details>

### CBOR Types - bytes_to_text

#### when converting byte values to text

#### returns correct ASCII text for lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [104, 105]  # h, i
val result = bytes_to_text(bytes)
expect(result).to_equal("hi")
```

</details>

#### returns correct ASCII text for uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [72, 73]  # H, I
val result = bytes_to_text(bytes)
expect(result).to_equal("HI")
```

</details>

#### returns correct text for digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [48, 49, 50]  # 0, 1, 2
val result = bytes_to_text(bytes)
expect(result).to_equal("012")
```

</details>

#### when converting empty byte array

#### returns empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = empty_i64_list()
val result = bytes_to_text(empty)
expect(result).to_equal("")
```

</details>

#### when roundtripping

#### text_to_bytes then bytes_to_text returns original

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single-char roundtrip (multi-char limited by runtime substring bug)
val original = "H"
val bts = text_to_bytes(original)
val roundtrip = bytes_to_text(bts)
expect(roundtrip).to_equal(original)
```

</details>

### CBOR Types - text_to_bytes extended chars

#### when converting additional lowercase letters

#### handles d through h

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("d")[0]).to_equal(100)
expect(text_to_bytes("e")[0]).to_equal(101)
expect(text_to_bytes("f")[0]).to_equal(102)
expect(text_to_bytes("g")[0]).to_equal(103)
expect(text_to_bytes("h")[0]).to_equal(104)
```

</details>

#### handles i through m

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("i")[0]).to_equal(105)
expect(text_to_bytes("j")[0]).to_equal(106)
expect(text_to_bytes("k")[0]).to_equal(107)
expect(text_to_bytes("l")[0]).to_equal(108)
expect(text_to_bytes("m")[0]).to_equal(109)
```

</details>

#### handles n through r

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("n")[0]).to_equal(110)
expect(text_to_bytes("o")[0]).to_equal(111)
expect(text_to_bytes("p")[0]).to_equal(112)
expect(text_to_bytes("q")[0]).to_equal(113)
expect(text_to_bytes("r")[0]).to_equal(114)
```

</details>

#### handles s through w

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("s")[0]).to_equal(115)
expect(text_to_bytes("t")[0]).to_equal(116)
expect(text_to_bytes("u")[0]).to_equal(117)
expect(text_to_bytes("v")[0]).to_equal(118)
expect(text_to_bytes("w")[0]).to_equal(119)
```

</details>

#### handles x through z

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("x")[0]).to_equal(120)
expect(text_to_bytes("y")[0]).to_equal(121)
expect(text_to_bytes("z")[0]).to_equal(122)
```

</details>

#### when converting additional uppercase letters

#### handles D through H

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("D")[0]).to_equal(68)
expect(text_to_bytes("E")[0]).to_equal(69)
expect(text_to_bytes("F")[0]).to_equal(70)
expect(text_to_bytes("G")[0]).to_equal(71)
expect(text_to_bytes("H")[0]).to_equal(72)
```

</details>

#### handles I through M

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("I")[0]).to_equal(73)
expect(text_to_bytes("J")[0]).to_equal(74)
expect(text_to_bytes("K")[0]).to_equal(75)
expect(text_to_bytes("L")[0]).to_equal(76)
expect(text_to_bytes("M")[0]).to_equal(77)
```

</details>

#### handles N through R

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("N")[0]).to_equal(78)
expect(text_to_bytes("O")[0]).to_equal(79)
expect(text_to_bytes("P")[0]).to_equal(80)
expect(text_to_bytes("Q")[0]).to_equal(81)
expect(text_to_bytes("R")[0]).to_equal(82)
```

</details>

#### handles S through W

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("S")[0]).to_equal(83)
expect(text_to_bytes("T")[0]).to_equal(84)
expect(text_to_bytes("U")[0]).to_equal(85)
expect(text_to_bytes("V")[0]).to_equal(86)
expect(text_to_bytes("W")[0]).to_equal(87)
```

</details>

#### handles X through Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("X")[0]).to_equal(88)
expect(text_to_bytes("Y")[0]).to_equal(89)
expect(text_to_bytes("Z")[0]).to_equal(90)
```

</details>

#### when converting digits

#### handles 3 through 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("\"")[0]).to_equal(34)
expect(text_to_bytes("$")[0]).to_equal(36)
expect(text_to_bytes("%")[0]).to_equal(37)
```

</details>

#### handles ampersand and apostrophe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("&")[0]).to_equal(38)
expect(text_to_bytes("'")[0]).to_equal(39)
```

</details>

#### handles parentheses and asterisk

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("(")[0]).to_equal(40)
expect(text_to_bytes(")")[0]).to_equal(41)
expect(text_to_bytes("*")[0]).to_equal(42)
```

</details>

#### handles plus comma minus period

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("+")[0]).to_equal(43)
expect(text_to_bytes(",")[0]).to_equal(44)
expect(text_to_bytes("-")[0]).to_equal(45)
expect(text_to_bytes(".")[0]).to_equal(46)
```

</details>

#### handles slash colon semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("/")[0]).to_equal(47)
expect(text_to_bytes(":")[0]).to_equal(58)
expect(text_to_bytes(";")[0]).to_equal(59)
```

</details>

#### handles angle brackets equals question

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("<")[0]).to_equal(60)
expect(text_to_bytes("=")[0]).to_equal(61)
expect(text_to_bytes(">")[0]).to_equal(62)
expect(text_to_bytes("?")[0]).to_equal(63)
```

</details>

#### handles brackets backslash caret underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("[")[0]).to_equal(91)
expect(text_to_bytes("\\")[0]).to_equal(92)
expect(text_to_bytes("]")[0]).to_equal(93)
expect(text_to_bytes("^")[0]).to_equal(94)
expect(text_to_bytes("_")[0]).to_equal(95)
```

</details>

#### handles pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_to_bytes("|")[0]).to_equal(124)
```

</details>

### CBOR Types - bytes_to_text extended chars

#### when converting additional lowercase byte values

#### handles d through h

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([100])).to_equal("d")
expect(bytes_to_text([101])).to_equal("e")
expect(bytes_to_text([102])).to_equal("f")
expect(bytes_to_text([103])).to_equal("g")
expect(bytes_to_text([104])).to_equal("h")
```

</details>

#### handles i through m

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([105])).to_equal("i")
expect(bytes_to_text([106])).to_equal("j")
expect(bytes_to_text([107])).to_equal("k")
expect(bytes_to_text([108])).to_equal("l")
expect(bytes_to_text([109])).to_equal("m")
```

</details>

#### handles n through r

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([110])).to_equal("n")
expect(bytes_to_text([111])).to_equal("o")
expect(bytes_to_text([112])).to_equal("p")
expect(bytes_to_text([113])).to_equal("q")
expect(bytes_to_text([114])).to_equal("r")
```

</details>

#### handles s through w

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([115])).to_equal("s")
expect(bytes_to_text([116])).to_equal("t")
expect(bytes_to_text([117])).to_equal("u")
expect(bytes_to_text([118])).to_equal("v")
expect(bytes_to_text([119])).to_equal("w")
```

</details>

#### handles x through z

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([120])).to_equal("x")
expect(bytes_to_text([121])).to_equal("y")
expect(bytes_to_text([122])).to_equal("z")
```

</details>

#### when converting additional uppercase byte values

#### handles D through H

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([68])).to_equal("D")
expect(bytes_to_text([69])).to_equal("E")
expect(bytes_to_text([70])).to_equal("F")
expect(bytes_to_text([71])).to_equal("G")
expect(bytes_to_text([72])).to_equal("H")
```

</details>

#### handles I through M

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([73])).to_equal("I")
expect(bytes_to_text([74])).to_equal("J")
expect(bytes_to_text([75])).to_equal("K")
expect(bytes_to_text([76])).to_equal("L")
expect(bytes_to_text([77])).to_equal("M")
```

</details>

#### handles N through R

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([78])).to_equal("N")
expect(bytes_to_text([79])).to_equal("O")
expect(bytes_to_text([80])).to_equal("P")
expect(bytes_to_text([81])).to_equal("Q")
expect(bytes_to_text([82])).to_equal("R")
```

</details>

#### handles S through W

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([83])).to_equal("S")
expect(bytes_to_text([84])).to_equal("T")
expect(bytes_to_text([85])).to_equal("U")
expect(bytes_to_text([86])).to_equal("V")
expect(bytes_to_text([87])).to_equal("W")
```

</details>

#### handles X through Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([88])).to_equal("X")
expect(bytes_to_text([89])).to_equal("Y")
expect(bytes_to_text([90])).to_equal("Z")
```

</details>

#### when converting digit byte values

#### handles 3 through 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([51])).to_equal("3")
expect(bytes_to_text([52])).to_equal("4")
expect(bytes_to_text([53])).to_equal("5")
expect(bytes_to_text([54])).to_equal("6")
expect(bytes_to_text([55])).to_equal("7")
expect(bytes_to_text([56])).to_equal("8")
expect(bytes_to_text([57])).to_equal("9")
```

</details>

#### when converting special character byte values

#### handles quote dollar percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([34])).to_equal("\"")
expect(bytes_to_text([36])).to_equal("$")
expect(bytes_to_text([37])).to_equal("%")
```

</details>

#### handles ampersand apostrophe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([38])).to_equal("&")
expect(bytes_to_text([39])).to_equal("'")
```

</details>

#### handles parentheses asterisk

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([40])).to_equal("(")
expect(bytes_to_text([41])).to_equal(")")
expect(bytes_to_text([42])).to_equal("*")
```

</details>

#### handles plus comma minus period

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([43])).to_equal("+")
expect(bytes_to_text([44])).to_equal(",")
expect(bytes_to_text([45])).to_equal("-")
expect(bytes_to_text([46])).to_equal(".")
```

</details>

#### handles slash colon semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([47])).to_equal("/")
expect(bytes_to_text([58])).to_equal(":")
expect(bytes_to_text([59])).to_equal(";")
```

</details>

#### handles angle brackets equals question

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([60])).to_equal("<")
expect(bytes_to_text([61])).to_equal("=")
expect(bytes_to_text([62])).to_equal(">")
expect(bytes_to_text([63])).to_equal("?")
```

</details>

#### handles brackets backslash caret underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([91])).to_equal("[")
expect(bytes_to_text([92])).to_equal("\\")
expect(bytes_to_text([93])).to_equal("]")
expect(bytes_to_text([94])).to_equal("^")
expect(bytes_to_text([95])).to_equal("_")
```

</details>

#### handles pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_text([124])).to_equal("|")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 73 |
| Active scenarios | 73 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
