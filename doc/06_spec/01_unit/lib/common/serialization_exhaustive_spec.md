# Serialization Exhaustive Branch Coverage Specification

> Purpose: Prove that char_code_safe range boundary chars.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Exhaustive Branch Coverage Specification

Purpose: Prove that char_code_safe range boundary chars.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-EXHAUSTIVE |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/serialization_exhaustive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that char_code_safe range boundary chars.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### char_code_safe range boundary chars

#### handles colon just past digit range

- handles colon just past digit range
- Verify: handles colon just past digit range
   - Expected: char_code_safe(":") equals `58`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles colon just past digit range")
step("Verify: handles colon just past digit range")
# @req: REQ-LIB-COMMON-001
expect(char_code_safe(":")).to_equal(58)
```

</details>

#### handles bracket just past uppercase range

- handles bracket just past uppercase range
- Verify: handles bracket just past uppercase range
   - Expected: char_code_safe("[") equals `91`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles bracket just past uppercase range")
step("Verify: handles bracket just past uppercase range")
expect(char_code_safe("[")).to_equal(91)
```

</details>

#### handles brace just past lowercase range

- handles brace just past lowercase range
- Verify: handles brace just past lowercase range
   - Expected: char_code_safe("\{") equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles brace just past lowercase range")
step("Verify: handles brace just past lowercase range")
expect(char_code_safe("\{")).to_equal(123)
```

</details>

#### handles slash before digit range

- handles slash before digit range
- Verify: handles slash before digit range
   - Expected: char_code_safe("/") equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles slash before digit range")
step("Verify: handles slash before digit range")
expect(char_code_safe("/")).to_equal(47)
```

</details>

#### handles at-sign before uppercase range

- handles at-sign before uppercase range
- Verify: handles at-sign before uppercase range
   - Expected: char_code_safe("@") equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles at-sign before uppercase range")
step("Verify: handles at-sign before uppercase range")
expect(char_code_safe("@")).to_equal(64)
```

</details>

#### handles backtick before lowercase range

- handles backtick before lowercase range
- Verify: handles backtick before lowercase range
   - Expected: char_code_safe("`") equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles backtick before lowercase range")
step("Verify: handles backtick before lowercase range")
expect(char_code_safe("`")).to_equal(96)
```

</details>

### detect_format compound OR branches

#### detects sdn for object starting with curly

- detects sdn for object starting with curly
- Verify: detects sdn for object starting with curly
   - Expected: detect_format("\{a: 1\}") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects sdn for object starting with curly")
step("Verify: detects sdn for object starting with curly")
expect(detect_format("\{a: 1\}")).to_equal("sdn")
```

</details>

#### detects sdn for array starting with bracket

- detects sdn for array starting with bracket
- Verify: detects sdn for array starting with bracket
   - Expected: detect_format("[1]") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects sdn for array starting with bracket")
step("Verify: detects sdn for array starting with bracket")
expect(detect_format("[1]")).to_equal("sdn")
```

</details>

#### detects sdn for true

- detects sdn for true
- Verify: detects sdn for true
   - Expected: detect_format("true") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects sdn for true")
step("Verify: detects sdn for true")
expect(detect_format("true")).to_equal("sdn")
```

</details>

#### detects sdn for false

- detects sdn for false
- Verify: detects sdn for false
   - Expected: detect_format("false") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects sdn for false")
step("Verify: detects sdn for false")
expect(detect_format("false")).to_equal("sdn")
```

</details>

#### detects sdn for nil

- detects sdn for nil
- Verify: detects sdn for nil
   - Expected: detect_format("nil") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects sdn for nil")
step("Verify: detects sdn for nil")
expect(detect_format("nil")).to_equal("sdn")
```

</details>

#### detects sdn for number after failing literal checks

- detects sdn for number after failing literal checks
- Verify: detects sdn for number after failing literal checks
   - Expected: detect_format("99") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects sdn for number after failing literal checks")
step("Verify: detects sdn for number after failing literal checks")
expect(detect_format("99")).to_equal("sdn")
```

</details>

#### returns unknown when no format matches

- returns unknown when no format matches
- Verify: returns unknown when no format matches
   - Expected: detect_format("xyz") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns unknown when no format matches")
step("Verify: returns unknown when no format matches")
expect(detect_format("xyz")).to_equal("unknown")
```

</details>

### is_valid_sdn compound OR

#### returns true when format is sdn

- returns true when format is sdn
- Verify: returns true when format is sdn
   - Expected: is_valid_sdn("42") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when format is sdn")
step("Verify: returns true when format is sdn")
expect(is_valid_sdn("42")).to_equal(true)
```

</details>

#### returns true when format is tagged

- returns true when format is tagged
- Verify: returns true when format is tagged
   - Expected: is_valid_sdn("@T\{x\}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true when format is tagged")
step("Verify: returns true when format is tagged")
expect(is_valid_sdn("@T\{x\}")).to_equal(true)
```

</details>

#### returns false when format is unknown

- returns false when format is unknown
- Verify: returns false when format is unknown
   - Expected: is_valid_sdn("abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false when format is unknown")
step("Verify: returns false when format is unknown")
expect(is_valid_sdn("abc")).to_equal(false)
```

</details>

### hex_to_digit compound OR branches

#### converts lowercase a

- converts lowercase a
- Verify: converts lowercase a
   - Expected: hex_to_digit("a") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase a")
step("Verify: converts lowercase a")
expect(hex_to_digit("a")).to_equal(10)
```

</details>

#### converts uppercase A

- converts uppercase A
- Verify: converts uppercase A
   - Expected: hex_to_digit("A") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts uppercase A")
step("Verify: converts uppercase A")
expect(hex_to_digit("A")).to_equal(10)
```

</details>

#### converts lowercase b

- converts lowercase b
- Verify: converts lowercase b
   - Expected: hex_to_digit("b") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase b")
step("Verify: converts lowercase b")
expect(hex_to_digit("b")).to_equal(11)
```

</details>

#### converts uppercase B

- converts uppercase B
- Verify: converts uppercase B
   - Expected: hex_to_digit("B") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts uppercase B")
step("Verify: converts uppercase B")
expect(hex_to_digit("B")).to_equal(11)
```

</details>

#### converts lowercase c

- converts lowercase c
- Verify: converts lowercase c
   - Expected: hex_to_digit("c") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase c")
step("Verify: converts lowercase c")
expect(hex_to_digit("c")).to_equal(12)
```

</details>

#### converts uppercase C

- converts uppercase C
- Verify: converts uppercase C
   - Expected: hex_to_digit("C") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts uppercase C")
step("Verify: converts uppercase C")
expect(hex_to_digit("C")).to_equal(12)
```

</details>

#### converts lowercase d

- converts lowercase d
- Verify: converts lowercase d
   - Expected: hex_to_digit("d") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase d")
step("Verify: converts lowercase d")
expect(hex_to_digit("d")).to_equal(13)
```

</details>

#### converts uppercase D

- converts uppercase D
- Verify: converts uppercase D
   - Expected: hex_to_digit("D") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts uppercase D")
step("Verify: converts uppercase D")
expect(hex_to_digit("D")).to_equal(13)
```

</details>

#### converts lowercase e

- converts lowercase e
- Verify: converts lowercase e
   - Expected: hex_to_digit("e") equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase e")
step("Verify: converts lowercase e")
expect(hex_to_digit("e")).to_equal(14)
```

</details>

#### converts uppercase E

- converts uppercase E
- Verify: converts uppercase E
   - Expected: hex_to_digit("E") equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts uppercase E")
step("Verify: converts uppercase E")
expect(hex_to_digit("E")).to_equal(14)
```

</details>

#### converts lowercase f

- converts lowercase f
- Verify: converts lowercase f
   - Expected: hex_to_digit("f") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase f")
step("Verify: converts lowercase f")
expect(hex_to_digit("f")).to_equal(15)
```

</details>

#### converts uppercase F

- converts uppercase F
- Verify: converts uppercase F
   - Expected: hex_to_digit("F") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts uppercase F")
step("Verify: converts uppercase F")
expect(hex_to_digit("F")).to_equal(15)
```

</details>

### is_numeric_text compound AND

#### accepts pure digits

- accepts pure digits
- Verify: accepts pure digits
   - Expected: is_numeric_text("123") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts pure digits")
step("Verify: accepts pure digits")
expect(is_numeric_text("123")).to_equal(true)
```

</details>

#### rejects colon in number

- rejects colon in number
- Verify: rejects colon in number
   - Expected: is_numeric_text("1:2") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects colon in number")
step("Verify: rejects colon in number")
expect(is_numeric_text("1:2")).to_equal(false)
```

</details>

#### rejects exclamation mark

- rejects exclamation mark
- Verify: rejects exclamation mark
   - Expected: is_numeric_text("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects exclamation mark")
step("Verify: rejects exclamation mark")
expect(is_numeric_text("!")).to_equal(false)
```

</details>

### unquote_string compound AND

#### returns string with opening quote but no closing

- returns string with opening quote but no closing
- Verify: returns string with opening quote but no closing
   - Expected: result equals `"abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns string with opening quote but no closing")
step("Verify: returns string with opening quote but no closing")
val result = unquote_string("\"abc")
expect(result).to_equal("\"abc")
```

</details>

#### returns string with no quotes

- returns string with no quotes
- Verify: returns string with no quotes
   - Expected: result equals `abc"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns string with no quotes")
step("Verify: returns string with no quotes")
val result = unquote_string("abc\"")
expect(result).to_equal("abc\"")
```

</details>

### get_version loop branches

#### extracts version with space before comma

- extracts version with space before comma
- Verify: extracts version with space before comma
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts version with space before comma")
step("Verify: extracts version with space before comma")
val versioned = "\{v: 5, data: x\}"
val result = get_version(versioned)
expect(result).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### returns nil for version with no comma

- returns nil for version with no comma
- Verify: returns nil for version with no comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for version with no comma")
step("Verify: returns nil for version with no comma")
val result = get_version("\{v: 123\}")
expect(result).to_be_nil()
```

</details>

### strip_version loop branches

#### strips version from short data

- strips version from short data
- Verify: strips version from short data
   - Expected: result equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips version from short data")
step("Verify: strips version from short data")
val versioned = add_version("x", 1)
val result = strip_version(versioned)
expect(result).to_equal("x")
```

</details>

#### handles version string that is just prefix

- handles version string that is just prefix
- Verify: handles version string that is just prefix
   - Expected: result equals `\{v: 1, dat\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles version string that is just prefix")
step("Verify: handles version string that is just prefix")
val result = strip_version("\{v: 1, dat\}")
# No "data: " found, returns original
expect(result).to_equal("\{v: 1, dat\}")
```

</details>

### write_varint boundary values

#### encodes 127 as single byte

- encodes 127 as single byte
- Verify: encodes 127 as single byte
   - Expected: result.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes 127 as single byte")
step("Verify: encodes 127 as single byte")
val result = write_varint(127)
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### encodes 128 as two bytes with continuation bit

- encodes 128 as two bytes with continuation bit
- Verify: encodes 128 as two bytes with continuation bit
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes 128 as two bytes with continuation bit")
step("Verify: encodes 128 as two bytes with continuation bit")
val result = write_varint(128)
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
val first_byte = result[0]
# First byte should have continuation bit set (>= 128)
expect(first_byte).to_be_greater_than(127)
```

</details>

#### encodes 255 as two bytes

- encodes 255 as two bytes
- Verify: encodes 255 as two bytes
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes 255 as two bytes")
step("Verify: encodes 255 as two bytes")
val result = write_varint(255)
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### read_varint loop termination

#### reads single-byte varint with byte < 128

- reads single-byte varint with byte < 128
- Verify: reads single-byte varint with byte < 128
   - Expected: result.0 equals `42`
   - Expected: result.1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads single-byte varint with byte < 128")
step("Verify: reads single-byte varint with byte < 128")
val result = read_varint([42], 0)
expect(result.0).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(result.1).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reads two-byte varint continuing past first byte

- reads two-byte varint continuing past first byte
- Verify: reads two-byte varint continuing past first byte
   - Expected: result.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads two-byte varint continuing past first byte")
step("Verify: reads two-byte varint continuing past first byte")
val encoded = write_varint(200)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(200)  # oracle: 200 — named expected value from the requirement
```

</details>

#### rejects negative offset

- rejects negative offset
- Verify: rejects negative offset
   - Expected: result.0 equals `0`
   - Expected: result.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects negative offset")
step("Verify: rejects negative offset")
val result = read_varint([42], 0 - 1)
expect(result.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### structural_hash_bool branches

#### returns 1 for true

- returns 1 for true
- Verify: returns 1 for true
   - Expected: structural_hash_bool(true) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 1 for true")
step("Verify: returns 1 for true")
expect(structural_hash_bool(true)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns 0 for false

- returns 0 for false
- Verify: returns 0 for false
   - Expected: structural_hash_bool(false) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for false")
step("Verify: returns 0 for false")
expect(structural_hash_bool(false)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### structural_hash_int xor branch

#### hashes 3 to non-zero

- hashes 3 to non-zero
- Verify: hashes 3 to non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes 3 to non-zero")
step("Verify: hashes 3 to non-zero")
val h = structural_hash_int(3)
expect(h).to_not_equal(0)
```

</details>

#### hashes 100 to non-zero

- hashes 100 to non-zero
- Verify: hashes 100 to non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes 100 to non-zero")
step("Verify: hashes 100 to non-zero")
val h = structural_hash_int(100)
expect(h).to_not_equal(0)
```

</details>

### char_code_safe exhaustive

#### covers all ASCII codes via serialize_text_bytes

- covers all ASCII codes via serialize_text_bytes
- Verify: covers all ASCII codes via serialize_text_bytes
   - Expected: r1[0] equals `type_text()`
   - Expected: r2[0] equals `type_text()`
   - Expected: r3[0] equals `type_text()`
   - Expected: r4[0] equals `type_text()`
   - Expected: r5[0] equals `type_text()`
   - Expected: r6[0] equals `type_text()`
   - Expected: r7[0] equals `type_text()`
   - Expected: r8[0] equals `type_text()`
   - Expected: r9[0] equals `type_text()`
   - Expected: r10[0] equals `type_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers all ASCII codes via serialize_text_bytes")
step("Verify: covers all ASCII codes via serialize_text_bytes")
# Binary serialize various strings to exercise char_code_safe for each char
val r1 = serialize_text_bytes(" !\"#$%&'()*+,-./")
expect(r1[0]).to_equal(type_text())

val r2 = serialize_text_bytes("0123456789")
expect(r2[0]).to_equal(type_text())

val r3 = serialize_text_bytes(":;<=>?@")
expect(r3[0]).to_equal(type_text())

val r4 = serialize_text_bytes("ABCDEFGHIJKLM")
expect(r4[0]).to_equal(type_text())

val r5 = serialize_text_bytes("NOPQRSTUVWXYZ")
expect(r5[0]).to_equal(type_text())

val r6 = serialize_text_bytes("[\\]^_`")
expect(r6[0]).to_equal(type_text())

val r7 = serialize_text_bytes("abcdefghijklm")
expect(r7[0]).to_equal(type_text())

val r8 = serialize_text_bytes("nopqrstuvwxyz")
expect(r8[0]).to_equal(type_text())

val r9 = serialize_text_bytes("\{|~")
expect(r9[0]).to_equal(type_text())

val r10 = serialize_text_bytes("\n\t\r")
expect(r10[0]).to_equal(type_text())
```

</details>

#### exercises individual char_code_safe for each remaining char

- exercises individual char_code_safe for each remaining char
- Verify: exercises individual char_code_safe for each remaining char
   - Expected: char_code_safe(" ") equals `32`
   - Expected: char_code_safe("!") equals `33`
   - Expected: char_code_safe("\"") equals `34`
   - Expected: char_code_safe("#") equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exercises individual char_code_safe for each remaining char")
step("Verify: exercises individual char_code_safe for each remaining char")
# Symbols not in other tests
expect(char_code_safe(" ")).to_equal(32)
expect(char_code_safe("!")).to_equal(33)
expect(char_code_safe("\"")).to_equal(34)
expect(char_code_safe("#")).to_equal(35)
```

</details>

#### exercises all digits individually

- exercises all digits individually
- Verify: exercises all digits individually
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
# @req REQ-SSPEC-LIB
step("exercises all digits individually")
step("Verify: exercises all digits individually")
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

#### exercises all lowercase individually

- exercises all lowercase individually
- Verify: exercises all lowercase individually
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
# @req REQ-SSPEC-LIB
step("exercises all lowercase individually")
step("Verify: exercises all lowercase individually")
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

#### exercises all uppercase individually

- exercises all uppercase individually
- Verify: exercises all uppercase individually
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
# @req REQ-SSPEC-LIB
step("exercises all uppercase individually")
step("Verify: exercises all uppercase individually")
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

### digit_to_hex exhaustive

#### covers all 16 hex digits

- covers all 16 hex digits
- Verify: covers all 16 hex digits
   - Expected: digit_to_hex(0) equals `0`
   - Expected: digit_to_hex(1) equals `1`
   - Expected: digit_to_hex(2) equals `2`
   - Expected: digit_to_hex(3) equals `3`
   - Expected: digit_to_hex(4) equals `4`
   - Expected: digit_to_hex(5) equals `5`
   - Expected: digit_to_hex(6) equals `6`
   - Expected: digit_to_hex(7) equals `7`
   - Expected: digit_to_hex(8) equals `8`
   - Expected: digit_to_hex(9) equals `9`
   - Expected: digit_to_hex(10) equals `a`
   - Expected: digit_to_hex(11) equals `b`
   - Expected: digit_to_hex(12) equals `c`
   - Expected: digit_to_hex(13) equals `d`
   - Expected: digit_to_hex(14) equals `e`
   - Expected: digit_to_hex(15) equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers all 16 hex digits")
step("Verify: covers all 16 hex digits")
expect(digit_to_hex(0)).to_equal("0")
expect(digit_to_hex(1)).to_equal("1")
expect(digit_to_hex(2)).to_equal("2")
expect(digit_to_hex(3)).to_equal("3")
expect(digit_to_hex(4)).to_equal("4")
expect(digit_to_hex(5)).to_equal("5")
expect(digit_to_hex(6)).to_equal("6")
expect(digit_to_hex(7)).to_equal("7")
expect(digit_to_hex(8)).to_equal("8")
expect(digit_to_hex(9)).to_equal("9")
expect(digit_to_hex(10)).to_equal("a")
expect(digit_to_hex(11)).to_equal("b")
expect(digit_to_hex(12)).to_equal("c")
expect(digit_to_hex(13)).to_equal("d")
expect(digit_to_hex(14)).to_equal("e")
expect(digit_to_hex(15)).to_equal("f")
```

</details>

### hex_to_digit exhaustive

#### covers all numeric hex digits

- covers all numeric hex digits
- Verify: covers all numeric hex digits
   - Expected: hex_to_digit("0") equals `0`
   - Expected: hex_to_digit("1") equals `1`
   - Expected: hex_to_digit("2") equals `2`
   - Expected: hex_to_digit("3") equals `3`
   - Expected: hex_to_digit("4") equals `4`
   - Expected: hex_to_digit("5") equals `5`
   - Expected: hex_to_digit("6") equals `6`
   - Expected: hex_to_digit("7") equals `7`
   - Expected: hex_to_digit("8") equals `8`
   - Expected: hex_to_digit("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers all numeric hex digits")
step("Verify: covers all numeric hex digits")
expect(hex_to_digit("0")).to_equal(0)
expect(hex_to_digit("1")).to_equal(1)
expect(hex_to_digit("2")).to_equal(2)
expect(hex_to_digit("3")).to_equal(3)
expect(hex_to_digit("4")).to_equal(4)
expect(hex_to_digit("5")).to_equal(5)
expect(hex_to_digit("6")).to_equal(6)
expect(hex_to_digit("7")).to_equal(7)
expect(hex_to_digit("8")).to_equal(8)
expect(hex_to_digit("9")).to_equal(9)
```

</details>

#### covers all lowercase letter hex digits

- covers all lowercase letter hex digits
- Verify: covers all lowercase letter hex digits
   - Expected: hex_to_digit("a") equals `10`
   - Expected: hex_to_digit("b") equals `11`
   - Expected: hex_to_digit("c") equals `12`
   - Expected: hex_to_digit("d") equals `13`
   - Expected: hex_to_digit("e") equals `14`
   - Expected: hex_to_digit("f") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers all lowercase letter hex digits")
step("Verify: covers all lowercase letter hex digits")
expect(hex_to_digit("a")).to_equal(10)
expect(hex_to_digit("b")).to_equal(11)
expect(hex_to_digit("c")).to_equal(12)
expect(hex_to_digit("d")).to_equal(13)
expect(hex_to_digit("e")).to_equal(14)
expect(hex_to_digit("f")).to_equal(15)
```

</details>

#### covers all uppercase letter hex digits

- covers all uppercase letter hex digits
- Verify: covers all uppercase letter hex digits
   - Expected: hex_to_digit("A") equals `10`
   - Expected: hex_to_digit("B") equals `11`
   - Expected: hex_to_digit("C") equals `12`
   - Expected: hex_to_digit("D") equals `13`
   - Expected: hex_to_digit("E") equals `14`
   - Expected: hex_to_digit("F") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers all uppercase letter hex digits")
step("Verify: covers all uppercase letter hex digits")
expect(hex_to_digit("A")).to_equal(10)
expect(hex_to_digit("B")).to_equal(11)
expect(hex_to_digit("C")).to_equal(12)
expect(hex_to_digit("D")).to_equal(13)
expect(hex_to_digit("E")).to_equal(14)
expect(hex_to_digit("F")).to_equal(15)
```

</details>

### char_to_digit_safe exhaustive

#### covers all digits 0 through 9

- covers all digits 0 through 9
- Verify: covers all digits 0 through 9
   - Expected: char_to_digit_safe("0") equals `0`
   - Expected: char_to_digit_safe("1") equals `1`
   - Expected: char_to_digit_safe("2") equals `2`
   - Expected: char_to_digit_safe("3") equals `3`
   - Expected: char_to_digit_safe("4") equals `4`
   - Expected: char_to_digit_safe("5") equals `5`
   - Expected: char_to_digit_safe("6") equals `6`
   - Expected: char_to_digit_safe("7") equals `7`
   - Expected: char_to_digit_safe("8") equals `8`
   - Expected: char_to_digit_safe("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers all digits 0 through 9")
step("Verify: covers all digits 0 through 9")
expect(char_to_digit_safe("0")).to_equal(0)
expect(char_to_digit_safe("1")).to_equal(1)
expect(char_to_digit_safe("2")).to_equal(2)
expect(char_to_digit_safe("3")).to_equal(3)
expect(char_to_digit_safe("4")).to_equal(4)
expect(char_to_digit_safe("5")).to_equal(5)
expect(char_to_digit_safe("6")).to_equal(6)
expect(char_to_digit_safe("7")).to_equal(7)
expect(char_to_digit_safe("8")).to_equal(8)
expect(char_to_digit_safe("9")).to_equal(9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0d56e929ba7d55adbe6519acabd07b966acd67774f106c54b7a47a8809e65bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0d56e929ba7d55adbe6519acabd07b966acd67774f106c54b7a47a8809e65bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0d56e929ba7d55adbe6519acabd07b966acd67774f106c54b7a47a8809e65bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/serialization_exhaustive_spec.spl
mirror: doc/06_spec/01_unit/lib/common/serialization_exhaustive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/serialization_exhaustive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/serialization_exhaustive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/serialization_exhaustive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 116 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/serialization_exhaustive_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles colon just past digit range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/serialization_exhaustive_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles bracket just past uppercase range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/serialization_exhaustive_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles brace just past lowercase range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
