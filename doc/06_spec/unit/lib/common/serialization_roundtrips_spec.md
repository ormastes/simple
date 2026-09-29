# Serialization Roundtrips and Extended Branch Coverage Specification

> Purpose: Prove that Serialization Roundtrips.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 86 | 86 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Roundtrips and Extended Branch Coverage Specification

Purpose: Prove that Serialization Roundtrips.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-ROUNDTRIPS |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/common/serialization_roundtrips_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Serialization Roundtrips.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Serialization Roundtrips

#### varint roundtrips

#### roundtrips various values

- roundtrips various values
- Verify: roundtrips various values
   - Expected: decoded.0 equals `values[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips various values")
step("Verify: roundtrips various values")
# @req: REQ-LIB-COMMON-001
val values = [0, 1, 127, 128, 256, 1000, -1, -128, -1000]
var i = 0
while i < values.len():
    val encoded = write_varint(values[i])
    val decoded = read_varint(encoded, 0)
    expect(decoded.0).to_equal(values[i])
    i = i + 1
```

</details>

#### string escape roundtrips

#### roundtrips strings with all special characters

- roundtrips strings with all special characters
- Verify: roundtrips strings with all special characters
   - Expected: roundtripped equals `inputs[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips strings with all special characters")
step("Verify: roundtrips strings with all special characters")
val inputs = ["", "hello", "say \"hi\"", "a\\b", "line1\nline2", "col1\tcol2", "cr\rhere"]
var i = 0
while i < inputs.len():
    val roundtripped = unescape_string(escape_string(inputs[i]))
    expect(roundtripped).to_equal(inputs[i])
    i = i + 1
```

</details>

#### quote/unquote roundtrips

#### roundtrips text through quote and unquote

- roundtrips text through quote and unquote
- Verify: roundtrips text through quote and unquote
   - Expected: roundtripped equals `inputs[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips text through quote and unquote")
step("Verify: roundtrips text through quote and unquote")
val inputs = ["", "simple", "with \"quotes\"", "with\nnewline"]
var i = 0
while i < inputs.len():
    val roundtripped = unquote_string(quote_string(inputs[i]))
    expect(roundtripped).to_equal(inputs[i])
    i = i + 1
```

</details>

#### hex roundtrips

#### roundtrips byte arrays through hex conversion

- roundtrips byte arrays through hex conversion
- Verify: roundtrips byte arrays through hex conversion
   - Expected: deep_equal_list_int(inputs[i], roundtripped) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips byte arrays through hex conversion")
step("Verify: roundtrips byte arrays through hex conversion")
val inputs = [[], [0], [255], [0, 127, 255], [16, 32, 48]]
var i = 0
while i < inputs.len():
    val roundtripped = hex_to_bytes(bytes_to_hex(inputs[i]))
    expect(deep_equal_list_int(inputs[i], roundtripped)).to_equal(true)
    i = i + 1
```

</details>

#### version roundtrips

#### roundtrips versioned data

- roundtrips versioned data
- Verify: roundtrips versioned data
   - Expected: get_version(versioned) equals `42`
   - Expected: strip_version(versioned) equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips versioned data")
step("Verify: roundtrips versioned data")
val data = "[1, 2, 3]"
val versioned = add_version(data, 42)
expect(get_version(versioned)).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(strip_version(versioned)).to_equal(data)
```

</details>

#### type tag roundtrips

#### roundtrips tagged data

- roundtrips tagged data
- Verify: roundtrips tagged data
   - Expected: get_type_tag(tagged) equals `CustomType`
   - Expected: strip_type_tag(tagged) equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips tagged data")
step("Verify: roundtrips tagged data")
val data = "inner content"
val tagged = tag_type(data, "CustomType")
expect(get_type_tag(tagged)).to_equal("CustomType")
expect(strip_type_tag(tagged)).to_equal(data)
```

</details>

### char_code_safe extended

#### returns correct codes for all lowercase letters

- returns correct codes for all lowercase letters
- Verify: returns correct codes for all lowercase letters
   - Expected: char_code_safe("a") equals `97`
   - Expected: char_code_safe("b") equals `98`
   - Expected: char_code_safe("c") equals `99`
   - Expected: char_code_safe("d") equals `100`
   - Expected: char_code_safe("e") equals `101`
   - Expected: char_code_safe("f") equals `102`
   - Expected: char_code_safe("g") equals `103`
   - Expected: char_code_safe("h") equals `104`
   - Expected: char_code_safe("i") equals `105`
   - Expected: char_code_safe("j") equals `106`
   - Expected: char_code_safe("k") equals `107`
   - Expected: char_code_safe("l") equals `108`
   - Expected: char_code_safe("m") equals `109`
   - Expected: char_code_safe("n") equals `110`
   - Expected: char_code_safe("o") equals `111`
   - Expected: char_code_safe("p") equals `112`
   - Expected: char_code_safe("q") equals `113`
   - Expected: char_code_safe("r") equals `114`
   - Expected: char_code_safe("s") equals `115`
   - Expected: char_code_safe("t") equals `116`
   - Expected: char_code_safe("u") equals `117`
   - Expected: char_code_safe("v") equals `118`
   - Expected: char_code_safe("w") equals `119`
   - Expected: char_code_safe("x") equals `120`
   - Expected: char_code_safe("y") equals `121`
   - Expected: char_code_safe("z") equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for all lowercase letters")
step("Verify: returns correct codes for all lowercase letters")
expect(char_code_safe("a")).to_equal(97)
expect(char_code_safe("b")).to_equal(98)
expect(char_code_safe("c")).to_equal(99)
expect(char_code_safe("d")).to_equal(100)
expect(char_code_safe("e")).to_equal(101)
expect(char_code_safe("f")).to_equal(102)
expect(char_code_safe("g")).to_equal(103)
expect(char_code_safe("h")).to_equal(104)
expect(char_code_safe("i")).to_equal(105)
expect(char_code_safe("j")).to_equal(106)
expect(char_code_safe("k")).to_equal(107)
expect(char_code_safe("l")).to_equal(108)
expect(char_code_safe("m")).to_equal(109)
expect(char_code_safe("n")).to_equal(110)
expect(char_code_safe("o")).to_equal(111)
expect(char_code_safe("p")).to_equal(112)
expect(char_code_safe("q")).to_equal(113)
expect(char_code_safe("r")).to_equal(114)
expect(char_code_safe("s")).to_equal(115)
expect(char_code_safe("t")).to_equal(116)
expect(char_code_safe("u")).to_equal(117)
expect(char_code_safe("v")).to_equal(118)
expect(char_code_safe("w")).to_equal(119)
expect(char_code_safe("x")).to_equal(120)
expect(char_code_safe("y")).to_equal(121)
expect(char_code_safe("z")).to_equal(122)
```

</details>

#### returns correct codes for all uppercase letters

- returns correct codes for all uppercase letters
- Verify: returns correct codes for all uppercase letters
   - Expected: char_code_safe("A") equals `65`
   - Expected: char_code_safe("B") equals `66`
   - Expected: char_code_safe("C") equals `67`
   - Expected: char_code_safe("D") equals `68`
   - Expected: char_code_safe("E") equals `69`
   - Expected: char_code_safe("F") equals `70`
   - Expected: char_code_safe("G") equals `71`
   - Expected: char_code_safe("H") equals `72`
   - Expected: char_code_safe("I") equals `73`
   - Expected: char_code_safe("J") equals `74`
   - Expected: char_code_safe("K") equals `75`
   - Expected: char_code_safe("L") equals `76`
   - Expected: char_code_safe("M") equals `77`
   - Expected: char_code_safe("N") equals `78`
   - Expected: char_code_safe("O") equals `79`
   - Expected: char_code_safe("P") equals `80`
   - Expected: char_code_safe("Q") equals `81`
   - Expected: char_code_safe("R") equals `82`
   - Expected: char_code_safe("S") equals `83`
   - Expected: char_code_safe("T") equals `84`
   - Expected: char_code_safe("U") equals `85`
   - Expected: char_code_safe("V") equals `86`
   - Expected: char_code_safe("W") equals `87`
   - Expected: char_code_safe("X") equals `88`
   - Expected: char_code_safe("Y") equals `89`
   - Expected: char_code_safe("Z") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for all uppercase letters")
step("Verify: returns correct codes for all uppercase letters")
expect(char_code_safe("A")).to_equal(65)
expect(char_code_safe("B")).to_equal(66)
expect(char_code_safe("C")).to_equal(67)
expect(char_code_safe("D")).to_equal(68)
expect(char_code_safe("E")).to_equal(69)
expect(char_code_safe("F")).to_equal(70)
expect(char_code_safe("G")).to_equal(71)
expect(char_code_safe("H")).to_equal(72)
expect(char_code_safe("I")).to_equal(73)
expect(char_code_safe("J")).to_equal(74)
expect(char_code_safe("K")).to_equal(75)
expect(char_code_safe("L")).to_equal(76)
expect(char_code_safe("M")).to_equal(77)
expect(char_code_safe("N")).to_equal(78)
expect(char_code_safe("O")).to_equal(79)
expect(char_code_safe("P")).to_equal(80)
expect(char_code_safe("Q")).to_equal(81)
expect(char_code_safe("R")).to_equal(82)
expect(char_code_safe("S")).to_equal(83)
expect(char_code_safe("T")).to_equal(84)
expect(char_code_safe("U")).to_equal(85)
expect(char_code_safe("V")).to_equal(86)
expect(char_code_safe("W")).to_equal(87)
expect(char_code_safe("X")).to_equal(88)
expect(char_code_safe("Y")).to_equal(89)
expect(char_code_safe("Z")).to_equal(90)
```

</details>

#### returns correct codes for all digits

- returns correct codes for all digits
- Verify: returns correct codes for all digits
   - Expected: char_code_safe("0") equals `48`
   - Expected: char_code_safe("1") equals `49`
   - Expected: char_code_safe("2") equals `50`
   - Expected: char_code_safe("3") equals `51`
   - Expected: char_code_safe("4") equals `52`
   - Expected: char_code_safe("5") equals `53`
   - Expected: char_code_safe("6") equals `54`
   - Expected: char_code_safe("7") equals `55`
   - Expected: char_code_safe("8") equals `56`
   - Expected: char_code_safe("9") equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for all digits")
step("Verify: returns correct codes for all digits")
expect(char_code_safe("0")).to_equal(48)
expect(char_code_safe("1")).to_equal(49)
expect(char_code_safe("2")).to_equal(50)
expect(char_code_safe("3")).to_equal(51)
expect(char_code_safe("4")).to_equal(52)
expect(char_code_safe("5")).to_equal(53)
expect(char_code_safe("6")).to_equal(54)
expect(char_code_safe("7")).to_equal(55)
expect(char_code_safe("8")).to_equal(56)
expect(char_code_safe("9")).to_equal(57)
```

</details>

#### returns correct codes for remaining symbols

- returns correct codes for remaining symbols
- Verify: returns correct codes for remaining symbols
   - Expected: char_code_safe(":") equals `58`
   - Expected: char_code_safe(";") equals `59`
   - Expected: char_code_safe("<") equals `60`
   - Expected: char_code_safe("=") equals `61`
   - Expected: char_code_safe(">") equals `62`
   - Expected: char_code_safe("?") equals `63`
   - Expected: char_code_safe("@") equals `64`
   - Expected: char_code_safe("[") equals `91`
   - Expected: char_code_safe("\\") equals `92`
   - Expected: char_code_safe("]") equals `93`
   - Expected: char_code_safe("^") equals `94`
   - Expected: char_code_safe("_") equals `95`
   - Expected: char_code_safe("`") equals `96`
   - Expected: char_code_safe("\{") equals `123`
   - Expected: char_code_safe("|") equals `124`
   - Expected: char_code_safe("\}") equals `125`
   - Expected: char_code_safe("~") equals `126`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for remaining symbols")
step("Verify: returns correct codes for remaining symbols")
expect(char_code_safe(":")).to_equal(58)
expect(char_code_safe(";")).to_equal(59)
expect(char_code_safe("<")).to_equal(60)
expect(char_code_safe("=")).to_equal(61)
expect(char_code_safe(">")).to_equal(62)
expect(char_code_safe("?")).to_equal(63)
expect(char_code_safe("@")).to_equal(64)
expect(char_code_safe("[")).to_equal(91)
expect(char_code_safe("\\")).to_equal(92)
expect(char_code_safe("]")).to_equal(93)
expect(char_code_safe("^")).to_equal(94)
expect(char_code_safe("_")).to_equal(95)
expect(char_code_safe("`")).to_equal(96)
expect(char_code_safe("\{")).to_equal(123)
expect(char_code_safe("|")).to_equal(124)
expect(char_code_safe("\}")).to_equal(125)
expect(char_code_safe("~")).to_equal(126)
```

</details>

#### returns correct codes for whitespace

- returns correct codes for whitespace
- Verify: returns correct codes for whitespace
   - Expected: char_code_safe("\n") equals `10`
   - Expected: char_code_safe("\t") equals `9`
   - Expected: char_code_safe("\r") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for whitespace")
step("Verify: returns correct codes for whitespace")
expect(char_code_safe("\n")).to_equal(10)
expect(char_code_safe("\t")).to_equal(9)
expect(char_code_safe("\r")).to_equal(13)
```

</details>

### char_from_code_safe extended

#### converts code 65 to A

- converts code 65 to A
- Verify: converts code 65 to A
   - Expected: char_from_code_safe(65) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 65 to A")
step("Verify: converts code 65 to A")
expect(char_from_code_safe(65)).to_equal("A")
```

</details>

#### converts code 97 to a

- converts code 97 to a
- Verify: converts code 97 to a
   - Expected: char_from_code_safe(97) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 97 to a")
step("Verify: converts code 97 to a")
expect(char_from_code_safe(97)).to_equal("a")
```

</details>

#### converts code 48 to 0

- converts code 48 to 0
- Verify: converts code 48 to 0
   - Expected: char_from_code_safe(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 48 to 0")
step("Verify: converts code 48 to 0")
expect(char_from_code_safe(48)).to_equal("0")
```

</details>

### write_varint extended

#### encodes 128 as two bytes

- encodes 128 as two bytes
- Verify: encodes 128 as two bytes
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 128 as two bytes")
step("Verify: encodes 128 as two bytes")
val result = write_varint(128)
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### encodes 16384 as three bytes

- encodes 16384 as three bytes
- Verify: encodes 16384 as three bytes
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 16384 as three bytes")
step("Verify: encodes 16384 as three bytes")
val result = write_varint(16384)
expect(result.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### encodes negative value with sign marker

- encodes negative value with sign marker
- Verify: encodes negative value with sign marker
   - Expected: result[0] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes negative value with sign marker")
step("Verify: encodes negative value with sign marker")
val result = write_varint(-42)
expect(result[0]).to_equal(255)  # oracle: 255 — named expected value from the requirement
expect(result.len()).to_be_greater_than(1)
```

</details>

#### roundtrips large positive

- roundtrips large positive
- Verify: roundtrips large positive
   - Expected: decoded.0 equals `100000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips large positive")
step("Verify: roundtrips large positive")
val encoded = write_varint(100000)
val decoded = read_varint(encoded, 0)
expect(decoded.0).to_equal(100000)  # oracle: 100000 — named expected value from the requirement
```

</details>

#### roundtrips large negative

- roundtrips large negative
- Verify: roundtrips large negative
   - Expected: decoded.0 equals `-100000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips large negative")
step("Verify: roundtrips large negative")
val encoded = write_varint(-100000)
val decoded = read_varint(encoded, 0)
expect(decoded.0).to_equal(-100000)  # oracle: -100000 — named expected value from the requirement
```

</details>

### read_varint extended

#### reports consumed bytes for multi-byte varint

- reports consumed bytes for multi-byte varint
- Verify: reports consumed bytes for multi-byte varint
   - Expected: decoded.1 equals `encoded.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports consumed bytes for multi-byte varint")
step("Verify: reports consumed bytes for multi-byte varint")
val encoded = write_varint(1000)
val decoded = read_varint(encoded, 0)
expect(decoded.1).to_equal(encoded.len())
```

</details>

#### reads varint at non-zero offset

- reads varint at non-zero offset
- Verify: reads varint at non-zero offset
   - Expected: decoded.0 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads varint at non-zero offset")
step("Verify: reads varint at non-zero offset")
var bytes = [99]
val encoded = write_varint(42)
var i = 0
while i < encoded.len():
    bytes = bytes.push(encoded[i])
    i = i + 1
val decoded = read_varint(bytes, 1)
expect(decoded.0).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### reports consumed bytes for negative varint

- reports consumed bytes for negative varint
- Verify: reports consumed bytes for negative varint
   - Expected: decoded.1 equals `encoded.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports consumed bytes for negative varint")
step("Verify: reports consumed bytes for negative varint")
val encoded = write_varint(-50)
val decoded = read_varint(encoded, 0)
expect(decoded.1).to_equal(encoded.len())
```

</details>

### serialize_text_bytes extended

#### encodes empty text

- encodes empty text
- Verify: encodes empty text
   - Expected: result[0] equals `type_text()`
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty text")
step("Verify: encodes empty text")
val result = serialize_text_bytes("")
expect(result[0]).to_equal(type_text())
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### encodes single character

- encodes single character
- Verify: encodes single character
   - Expected: result[0] equals `type_text()`
   - Expected: last equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes single character")
step("Verify: encodes single character")
val result = serialize_text_bytes("A")
expect(result[0]).to_equal(type_text())
val last = result[result.len() - 1]
expect(last).to_equal(65)  # oracle: 65 — named expected value from the requirement
```

</details>

#### encodes multi-character text

- encodes multi-character text
- Verify: encodes multi-character text
   - Expected: result[0] equals `type_text()`
   - Expected: second_last equals `65`
   - Expected: last equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes multi-character text")
step("Verify: encodes multi-character text")
val result = serialize_text_bytes("AB")
expect(result[0]).to_equal(type_text())
val second_last = result[result.len() - 2]
val last = result[result.len() - 1]
expect(second_last).to_equal(65)  # oracle: 65 — named expected value from the requirement
expect(last).to_equal(66)  # oracle: 66 — named expected value from the requirement
```

</details>

### escape_string extended

#### escapes double quote alone

- escapes double quote alone
- Verify: escapes double quote alone
   - Expected: result equals `\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes double quote alone")
step("Verify: escapes double quote alone")
val result = escape_string("\"")
expect(result).to_equal("\\\"")
```

</details>

#### escapes backslash alone

- escapes backslash alone
- Verify: escapes backslash alone
   - Expected: result equals `\\\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslash alone")
step("Verify: escapes backslash alone")
val result = escape_string("\\")
expect(result).to_equal("\\\\")
```

</details>

#### escapes tab alone

- escapes tab alone
- Verify: escapes tab alone
   - Expected: result equals `\\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes tab alone")
step("Verify: escapes tab alone")
val result = escape_string("\t")
expect(result).to_equal("\\t")
```

</details>

#### escapes carriage return alone

- escapes carriage return alone
- Verify: escapes carriage return alone
   - Expected: result equals `\\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes carriage return alone")
step("Verify: escapes carriage return alone")
val result = escape_string("\r")
expect(result).to_equal("\\r")
```

</details>

#### does not escape normal chars

- does not escape normal chars
- Verify: does not escape normal chars
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not escape normal chars")
step("Verify: does not escape normal chars")
val result = escape_string("abc")
expect(result).to_equal("abc")
```

</details>

### unescape_string extended

#### unescapes backslash-quote alone

- unescapes backslash-quote alone
- Verify: unescapes backslash-quote alone
   - Expected: result equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-quote alone")
step("Verify: unescapes backslash-quote alone")
val result = unescape_string("\\\"")
expect(result).to_equal("\"")
```

</details>

#### unescapes backslash-backslash alone

- unescapes backslash-backslash alone
- Verify: unescapes backslash-backslash alone
   - Expected: result equals `\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-backslash alone")
step("Verify: unescapes backslash-backslash alone")
val result = unescape_string("\\\\")
expect(result).to_equal("\\")
```

</details>

#### handles unknown escape code

- handles unknown escape code
- Verify: handles unknown escape code
   - Expected: result equals `\\x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown escape code")
step("Verify: handles unknown escape code")
val result = unescape_string("\\x")
expect(result).to_equal("\\x")
```

</details>

#### handles trailing backslash

- handles trailing backslash
- Verify: handles trailing backslash
   - Expected: result equals `abc\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles trailing backslash")
step("Verify: handles trailing backslash")
val result = unescape_string("abc\\")
expect(result).to_equal("abc\\")
```

</details>

#### handles multiple escapes in sequence

- handles multiple escapes in sequence
- Verify: handles multiple escapes in sequence
   - Expected: result equals `\n\t\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple escapes in sequence")
step("Verify: handles multiple escapes in sequence")
val result = unescape_string("\\n\\t\\r")
expect(result).to_equal("\n\t\r")
```

</details>

### unquote_string extended

#### returns single char unchanged

- returns single char unchanged
- Verify: returns single char unchanged
   - Expected: result equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single char unchanged")
step("Verify: returns single char unchanged")
val result = unquote_string("x")
expect(result).to_equal("x")
```

</details>

#### returns non-quoted two-char string unchanged

- returns non-quoted two-char string unchanged
- Verify: returns non-quoted two-char string unchanged
   - Expected: result equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-quoted two-char string unchanged")
step("Verify: returns non-quoted two-char string unchanged")
val result = unquote_string("ab")
expect(result).to_equal("ab")
```

</details>

#### unquotes minimal quoted string

- unquotes minimal quoted string
- Verify: unquotes minimal quoted string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unquotes minimal quoted string")
step("Verify: unquotes minimal quoted string")
val result = unquote_string("\"\"")
expect(result).to_equal("")
```

</details>

### serialize_int_bytes extended

#### serializes large positive integer

- serializes large positive integer
- Verify: serializes large positive integer
   - Expected: result[0] equals `type_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes large positive integer")
step("Verify: serializes large positive integer")
val result = serialize_int_bytes(100000)
expect(result[0]).to_equal(type_int())
expect(result.len()).to_be_greater_than(2)
```

</details>

#### serializes large negative integer

- serializes large negative integer
- Verify: serializes large negative integer
   - Expected: result[0] equals `type_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes large negative integer")
step("Verify: serializes large negative integer")
val result = serialize_int_bytes(-100000)
expect(result[0]).to_equal(type_int())
```

</details>

### serialize_bool_bytes extended

#### has exactly two bytes for true

- has exactly two bytes for true
- Verify: has exactly two bytes for true
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has exactly two bytes for true")
step("Verify: has exactly two bytes for true")
val result = serialize_bool_bytes(true)
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### has exactly two bytes for false

- has exactly two bytes for false
- Verify: has exactly two bytes for false
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has exactly two bytes for false")
step("Verify: has exactly two bytes for false")
val result = serialize_bool_bytes(false)
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### detect_format extended

#### returns unknown for tuple starting with paren

- returns unknown for tuple starting with paren
- Verify: returns unknown for tuple starting with paren
   - Expected: detect_format("(1, 2)") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for tuple starting with paren")
step("Verify: returns unknown for tuple starting with paren")
expect(detect_format("(1, 2)")).to_equal("unknown")
```

</details>

#### detects sdn for negative number

- detects sdn for negative number
- Verify: detects sdn for negative number
   - Expected: detect_format("-42") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for negative number")
step("Verify: detects sdn for negative number")
expect(detect_format("-42")).to_equal("sdn")
```

</details>

#### returns unknown for single special char

- returns unknown for single special char
- Verify: returns unknown for single special char
   - Expected: detect_format("~") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for single special char")
step("Verify: returns unknown for single special char")
expect(detect_format("~")).to_equal("unknown")
```

</details>

### is_valid_sdn extended

#### returns true for numeric string

- returns true for numeric string
- Verify: returns true for numeric string
   - Expected: is_valid_sdn("42") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for numeric string")
step("Verify: returns true for numeric string")
expect(is_valid_sdn("42")).to_equal(true)
```

</details>

#### returns true for quoted text

- returns true for quoted text
- Verify: returns true for quoted text
   - Expected: is_valid_sdn("\"hello\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for quoted text")
step("Verify: returns true for quoted text")
expect(is_valid_sdn("\"hello\"")).to_equal(true)
```

</details>

#### returns false for single char

- returns false for single char
- Verify: returns false for single char
   - Expected: is_valid_sdn("x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for single char")
step("Verify: returns false for single char")
expect(is_valid_sdn("x")).to_equal(false)
```

</details>

### get_type_tag extended

#### extracts single char tag

- extracts single char tag
- Verify: extracts single char tag
   - Expected: result equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts single char tag")
step("Verify: extracts single char tag")
val result = get_type_tag("@X\{v\}")
expect(result).to_equal("X")
```

</details>

#### extracts long tag name

- extracts long tag name
- Verify: extracts long tag name
   - Expected: result equals `VeryLongTypeName`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts long tag name")
step("Verify: extracts long tag name")
val result = get_type_tag("@VeryLongTypeName\{v\}")
expect(result).to_equal("VeryLongTypeName")
```

</details>

#### returns nil for at-sign only

- returns nil for at-sign only
- Verify: returns nil for at-sign only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for at-sign only")
step("Verify: returns nil for at-sign only")
val result = get_type_tag("@ab")
expect(result).to_be_nil()
```

</details>

### strip_type_tag extended

#### strips single char tag

- strips single char tag
- Verify: strips single char tag
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips single char tag")
step("Verify: strips single char tag")
val result = strip_type_tag("@X\{hello\}")
expect(result).to_equal("hello")
```

</details>

#### strips tag with empty content

- strips tag with empty content
- Verify: strips tag with empty content
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips tag with empty content")
step("Verify: strips tag with empty content")
val result = strip_type_tag("@T\{\}")
expect(result).to_equal("")
```

</details>

### get_version extended

#### extracts single digit version

- extracts single digit version
- Verify: extracts single digit version
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts single digit version")
step("Verify: extracts single digit version")
val versioned = add_version("x", 1)
val result = get_version(versioned)
expect(result).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### extracts multi-digit version

- extracts multi-digit version
- Verify: extracts multi-digit version
   - Expected: result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multi-digit version")
step("Verify: extracts multi-digit version")
val versioned = add_version("x", 99)
val result = get_version(versioned)
expect(result).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

### strip_version extended

#### strips version with complex data

- strips version with complex data
- Verify: strips version with complex data
   - Expected: result equals `[1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips version with complex data")
step("Verify: strips version with complex data")
val versioned = add_version("[1, 2, 3]", 10)
val result = strip_version(versioned)
expect(result).to_equal("[1, 2, 3]")
```

</details>

#### strips version with text data

- strips version with text data
- Verify: strips version with text data
   - Expected: result equals `"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips version with text data")
step("Verify: strips version with text data")
val versioned = add_version("\"hello\"", 2)
val result = strip_version(versioned)
expect(result).to_equal("\"hello\"")
```

</details>

### parse_int_safe extended

#### parses single digit

- parses single digit
- Verify: parses single digit
   - Expected: parse_int_safe("5") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single digit")
step("Verify: parses single digit")
expect(parse_int_safe("5")).to_equal(5)
```

</details>

#### parses large number

- parses large number
- Verify: parses large number
   - Expected: parse_int_safe("12345") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses large number")
step("Verify: parses large number")
expect(parse_int_safe("12345")).to_equal(12345)
```

</details>

#### parses negative with digits after

- parses negative with digits after
- Verify: parses negative with digits after
   - Expected: parse_int_safe("-123") equals `-123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses negative with digits after")
step("Verify: parses negative with digits after")
expect(parse_int_safe("-123")).to_equal(-123)
```

</details>

#### stops at first non-digit in middle

- stops at first non-digit in middle
- Verify: stops at first non-digit in middle
   - Expected: parse_int_safe("5abc3") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at first non-digit in middle")
step("Verify: stops at first non-digit in middle")
expect(parse_int_safe("5abc3")).to_equal(5)
```

</details>

### digit_to_hex extended

#### covers all low digits via int_to_hex

- covers all low digits via int_to_hex
- Verify: covers all low digits via int_to_hex
   - Expected: int_to_hex(0) equals `00`
   - Expected: int_to_hex(1) equals `01`
   - Expected: int_to_hex(2) equals `02`
   - Expected: int_to_hex(3) equals `03`
   - Expected: int_to_hex(4) equals `04`
   - Expected: int_to_hex(5) equals `05`
   - Expected: int_to_hex(6) equals `06`
   - Expected: int_to_hex(7) equals `07`
   - Expected: int_to_hex(8) equals `08`
   - Expected: int_to_hex(9) equals `09`
   - Expected: int_to_hex(10) equals `0a`
   - Expected: int_to_hex(11) equals `0b`
   - Expected: int_to_hex(12) equals `0c`
   - Expected: int_to_hex(13) equals `0d`
   - Expected: int_to_hex(14) equals `0e`
   - Expected: int_to_hex(15) equals `0f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers all low digits via int_to_hex")
step("Verify: covers all low digits via int_to_hex")
expect(int_to_hex(0)).to_equal("00")
expect(int_to_hex(1)).to_equal("01")
expect(int_to_hex(2)).to_equal("02")
expect(int_to_hex(3)).to_equal("03")
expect(int_to_hex(4)).to_equal("04")
expect(int_to_hex(5)).to_equal("05")
expect(int_to_hex(6)).to_equal("06")
expect(int_to_hex(7)).to_equal("07")
expect(int_to_hex(8)).to_equal("08")
expect(int_to_hex(9)).to_equal("09")
expect(int_to_hex(10)).to_equal("0a")
expect(int_to_hex(11)).to_equal("0b")
expect(int_to_hex(12)).to_equal("0c")
expect(int_to_hex(13)).to_equal("0d")
expect(int_to_hex(14)).to_equal("0e")
expect(int_to_hex(15)).to_equal("0f")
```

</details>

#### covers all high digits via int_to_hex

- covers all high digits via int_to_hex
- Verify: covers all high digits via int_to_hex
   - Expected: int_to_hex(16) equals `10`
   - Expected: int_to_hex(32) equals `20`
   - Expected: int_to_hex(160) equals `a0`
   - Expected: int_to_hex(176) equals `b0`
   - Expected: int_to_hex(192) equals `c0`
   - Expected: int_to_hex(208) equals `d0`
   - Expected: int_to_hex(224) equals `e0`
   - Expected: int_to_hex(240) equals `f0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers all high digits via int_to_hex")
step("Verify: covers all high digits via int_to_hex")
expect(int_to_hex(16)).to_equal("10")
expect(int_to_hex(32)).to_equal("20")
expect(int_to_hex(160)).to_equal("a0")
expect(int_to_hex(176)).to_equal("b0")
expect(int_to_hex(192)).to_equal("c0")
expect(int_to_hex(208)).to_equal("d0")
expect(int_to_hex(224)).to_equal("e0")
expect(int_to_hex(240)).to_equal("f0")
```

</details>

### hex_to_digit extended

#### converts all lowercase hex digits

- converts all lowercase hex digits
- Verify: converts all lowercase hex digits
   - Expected: result[0] equals `10`
   - Expected: result[1] equals `11`
   - Expected: result[2] equals `12`
   - Expected: result[3] equals `13`
   - Expected: result[4] equals `14`
   - Expected: result[5] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts all lowercase hex digits")
step("Verify: converts all lowercase hex digits")
val result = hex_to_bytes("0a0b0c0d0e0f")
expect(result[0]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(result[1]).to_equal(11)  # oracle: 11 — named expected value from the requirement
expect(result[2]).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(result[3]).to_equal(13)  # oracle: 13 — named expected value from the requirement
expect(result[4]).to_equal(14)  # oracle: 14 — named expected value from the requirement
expect(result[5]).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

#### converts all uppercase hex digits

- converts all uppercase hex digits
- Verify: converts all uppercase hex digits
   - Expected: result[0] equals `10`
   - Expected: result[1] equals `11`
   - Expected: result[2] equals `12`
   - Expected: result[3] equals `13`
   - Expected: result[4] equals `14`
   - Expected: result[5] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts all uppercase hex digits")
step("Verify: converts all uppercase hex digits")
val result = hex_to_bytes("0A0B0C0D0E0F")
expect(result[0]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(result[1]).to_equal(11)  # oracle: 11 — named expected value from the requirement
expect(result[2]).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(result[3]).to_equal(13)  # oracle: 13 — named expected value from the requirement
expect(result[4]).to_equal(14)  # oracle: 14 — named expected value from the requirement
expect(result[5]).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

#### converts all numeric digits

- converts all numeric digits
- Verify: converts all numeric digits
   - Expected: result[0] equals `0`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `2`
   - Expected: result[3] equals `3`
   - Expected: result[4] equals `4`
   - Expected: result[5] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts all numeric digits")
step("Verify: converts all numeric digits")
val result = hex_to_bytes("000102030405060708090a")
expect(result[0]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result[2]).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result[3]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result[4]).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(result[5]).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### deep_equal extended

#### detects mismatch at last position in int list

- detects mismatch at last position in int list
- Verify: detects mismatch at last position in int list
   - Expected: deep_equal_list_int([1, 2, 3], [1, 2, 4]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects mismatch at last position in int list")
step("Verify: detects mismatch at last position in int list")
expect(deep_equal_list_int([1, 2, 3], [1, 2, 4])).to_equal(false)
```

</details>

#### detects mismatch at first position in int list

- detects mismatch at first position in int list
- Verify: detects mismatch at first position in int list
   - Expected: deep_equal_list_int([9, 2, 3], [1, 2, 3]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects mismatch at first position in int list")
step("Verify: detects mismatch at first position in int list")
expect(deep_equal_list_int([9, 2, 3], [1, 2, 3])).to_equal(false)
```

</details>

#### detects mismatch in single element text list

- detects mismatch in single element text list
- Verify: detects mismatch in single element text list
   - Expected: deep_equal_list_text(["a"], ["b"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects mismatch in single element text list")
step("Verify: detects mismatch in single element text list")
expect(deep_equal_list_text(["a"], ["b"])).to_equal(false)
```

</details>

#### compares long equal int lists

- compares long equal int lists
- Verify: compares long equal int lists
   - Expected: deep_equal_list_int([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares long equal int lists")
step("Verify: compares long equal int lists")
expect(deep_equal_list_int([1, 2, 3, 4, 5], [1, 2, 3, 4, 5])).to_equal(true)
```

</details>

#### compares long equal text lists

- compares long equal text lists
- Verify: compares long equal text lists
   - Expected: deep_equal_list_text(["a", "b", "c"], ["a", "b", "c"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares long equal text lists")
step("Verify: compares long equal text lists")
expect(deep_equal_list_text(["a", "b", "c"], ["a", "b", "c"])).to_equal(true)
```

</details>

### structural_hash extended

#### hashes zero integer

- hashes zero integer
- Verify: hashes zero integer
   - Expected: h equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes zero integer")
step("Verify: hashes zero integer")
val h = structural_hash_int(0)
expect(h).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### hashes small positive integer

- hashes small positive integer
- Verify: hashes small positive integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes small positive integer")
step("Verify: hashes small positive integer")
val h = structural_hash_int(1)
expect(h).to_not_equal(0)
```

</details>

#### hashes negative integer

- hashes negative integer
- Verify: hashes negative integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes negative integer")
step("Verify: hashes negative integer")
val h = structural_hash_int(-1)
expect(h).to_not_equal(0)
```

</details>

#### hashes single-element int list

- hashes single-element int list
- Verify: hashes single-element int list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes single-element int list")
step("Verify: hashes single-element int list")
val h = structural_hash_list_int([1])
expect(h).to_not_equal(0)
```

</details>

#### combines two small hashes

- combines two small hashes
- Verify: combines two small hashes
   - Expected: h equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines two small hashes")
step("Verify: combines two small hashes")
val h = combine_hashes(1, 2)
expect(h).to_equal(33)  # oracle: 33 — named expected value from the requirement
```

</details>

### is_numeric_text extended

#### returns true for large negative number

- returns true for large negative number
- Verify: returns true for large negative number
   - Expected: is_numeric_text("-99999") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for large negative number")
step("Verify: returns true for large negative number")
expect(is_numeric_text("-99999")).to_equal(true)
```

</details>

#### returns false for negative with non-digit

- returns false for negative with non-digit
- Verify: returns false for negative with non-digit
   - Expected: is_numeric_text("-12a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for negative with non-digit")
step("Verify: returns false for negative with non-digit")
expect(is_numeric_text("-12a")).to_equal(false)
```

</details>

#### returns false for decimal point

- returns false for decimal point
- Verify: returns false for decimal point
   - Expected: is_numeric_text("3.14") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for decimal point")
step("Verify: returns false for decimal point")
expect(is_numeric_text("3.14")).to_equal(false)
```

</details>

### write_bytes extended

#### writes large byte array

- writes large byte array
- Verify: writes large byte array
   - Expected: result[0] equals `10`
   - Expected: result.len() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes large byte array")
step("Verify: writes large byte array")
val input = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val result = write_bytes(input)
expect(result[0]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(result.len()).to_equal(11)  # oracle: 11 — named expected value from the requirement
```

</details>

### read_bytes extended

#### reads from middle of array

- reads from middle of array
- Verify: reads from middle of array
   - Expected: data.len() equals `2`
   - Expected: data[0] equals `30`
   - Expected: data[1] equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads from middle of array")
step("Verify: reads from middle of array")
val bytes = [10, 20, 30, 40, 50]
val result = read_bytes(bytes, 2, 2)
val data = result.0
expect(data.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(data[0]).to_equal(30)  # oracle: 30 — named expected value from the requirement
expect(data[1]).to_equal(40)  # oracle: 40 — named expected value from the requirement
```

</details>

#### reads single byte

- reads single byte
- Verify: reads single byte
   - Expected: data.len() equals `1`
   - Expected: data[0] equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads single byte")
step("Verify: reads single byte")
val result = read_bytes([99], 0, 1)
val data = result.0
expect(data.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(data[0]).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

### Compression Markers extended

#### marks and detects long content

- marks and detects long content
- Verify: marks and detects long content
   - Expected: is_compressed(marked) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks and detects long content")
step("Verify: marks and detects long content")
val marked = mark_compressed("a long piece of content here")
expect(is_compressed(marked)).to_equal(true)
```

</details>

#### returns false for encrypted marker

- returns false for encrypted marker
- Verify: returns false for encrypted marker
   - Expected: is_compressed(encrypted) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for encrypted marker")
step("Verify: returns false for encrypted marker")
val encrypted = mark_encrypted("secret")
expect(is_compressed(encrypted)).to_equal(false)
```

</details>

### Encryption Markers extended

#### marks and detects long content

- marks and detects long content
- Verify: marks and detects long content
   - Expected: is_encrypted(marked) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks and detects long content")
step("Verify: marks and detects long content")
val marked = mark_encrypted("a long piece of content here")
expect(is_encrypted(marked)).to_equal(true)
```

</details>

#### returns false for compressed marker

- returns false for compressed marker
- Verify: returns false for compressed marker
   - Expected: is_encrypted(compressed) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for compressed marker")
step("Verify: returns false for compressed marker")
val compressed = mark_compressed("stuff")
expect(is_encrypted(compressed)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 86 |
| Active scenarios | 86 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc2d4117cbe2be01c708fbccaaf7b523d003a66982d71d14ddac9f35c70aa3da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc2d4117cbe2be01c708fbccaaf7b523d003a66982d71d14ddac9f35c70aa3da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc2d4117cbe2be01c708fbccaaf7b523d003a66982d71d14ddac9f35c70aa3da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/serialization_roundtrips_spec.spl
mirror: doc/06_spec/unit/lib/common/serialization_roundtrips_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/serialization_roundtrips_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/serialization_roundtrips_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/serialization_roundtrips_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 86 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/serialization_roundtrips_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'roundtrips various values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_roundtrips_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'roundtrips strings with all special characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_roundtrips_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'roundtrips text through quote and unquote' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
