# Serialization Primitives Coverage Specification

> Purpose: Prove that Type Constants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Primitives Coverage Specification

Purpose: Prove that Type Constants.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-PRIMITIVES |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/common/serialization_primitives_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Type Constants.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Type Constants

#### returns correct values for all type tags

- returns correct values for all type tags
- Verify: returns correct values for all type tags
   - Expected: type_nil() equals `0`
   - Expected: type_bool() equals `1`
   - Expected: type_int() equals `2`
   - Expected: type_float() equals `3`
   - Expected: type_text() equals `4`
   - Expected: type_list() equals `5`
   - Expected: type_tuple() equals `6`
   - Expected: type_dict() equals `7`
   - Expected: type_custom() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct values for all type tags")
step("Verify: returns correct values for all type tags")
# @req: REQ-LIB-COMMON-001
expect(type_nil()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(type_bool()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(type_int()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(type_float()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(type_text()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(type_list()).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(type_tuple()).to_equal(6)  # oracle: 6 — named expected value from the requirement
expect(type_dict()).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(type_custom()).to_equal(8)  # oracle: 8 — named expected value from the requirement
```

</details>

### char_code_safe

#### printable symbols

#### returns correct code for space

- returns correct code for space
- Verify: returns correct code for space
   - Expected: char_code_safe(" ") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct code for space")
step("Verify: returns correct code for space")
expect(char_code_safe(" ")).to_equal(32)
```

</details>

#### returns correct code for exclamation

- returns correct code for exclamation
- Verify: returns correct code for exclamation
   - Expected: char_code_safe("!") equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct code for exclamation")
step("Verify: returns correct code for exclamation")
expect(char_code_safe("!")).to_equal(33)
```

</details>

#### returns correct code for double quote

- returns correct code for double quote
- Verify: returns correct code for double quote
   - Expected: char_code_safe("\"") equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct code for double quote")
step("Verify: returns correct code for double quote")
expect(char_code_safe("\"")).to_equal(34)
```

</details>

#### returns correct code for hash

- returns correct code for hash
- Verify: returns correct code for hash
   - Expected: char_code_safe("#") equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct code for hash")
step("Verify: returns correct code for hash")
expect(char_code_safe("#")).to_equal(35)
```

</details>

#### returns correct code for various symbols

- returns correct code for various symbols
- Verify: returns correct code for various symbols
   - Expected: char_code_safe("$") equals `36`
   - Expected: char_code_safe("%") equals `37`
   - Expected: char_code_safe("&") equals `38`
   - Expected: char_code_safe("'") equals `39`
   - Expected: char_code_safe("(") equals `40`
   - Expected: char_code_safe(")") equals `41`
   - Expected: char_code_safe("*") equals `42`
   - Expected: char_code_safe("+") equals `43`
   - Expected: char_code_safe(",") equals `44`
   - Expected: char_code_safe("-") equals `45`
   - Expected: char_code_safe(".") equals `46`
   - Expected: char_code_safe("/") equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct code for various symbols")
step("Verify: returns correct code for various symbols")
expect(char_code_safe("$")).to_equal(36)
expect(char_code_safe("%")).to_equal(37)
expect(char_code_safe("&")).to_equal(38)
expect(char_code_safe("'")).to_equal(39)
expect(char_code_safe("(")).to_equal(40)
expect(char_code_safe(")")).to_equal(41)
expect(char_code_safe("*")).to_equal(42)
expect(char_code_safe("+")).to_equal(43)
expect(char_code_safe(",")).to_equal(44)
expect(char_code_safe("-")).to_equal(45)
expect(char_code_safe(".")).to_equal(46)
expect(char_code_safe("/")).to_equal(47)
```

</details>

#### digits

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

#### punctuation after digits

#### returns correct codes for colon through at-sign

- returns correct codes for colon through at-sign
- Verify: returns correct codes for colon through at-sign
   - Expected: char_code_safe(":") equals `58`
   - Expected: char_code_safe(";") equals `59`
   - Expected: char_code_safe("<") equals `60`
   - Expected: char_code_safe("=") equals `61`
   - Expected: char_code_safe(">") equals `62`
   - Expected: char_code_safe("@") equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for colon through at-sign")
step("Verify: returns correct codes for colon through at-sign")
expect(char_code_safe(":")).to_equal(58)
expect(char_code_safe(";")).to_equal(59)
expect(char_code_safe("<")).to_equal(60)
expect(char_code_safe("=")).to_equal(61)
expect(char_code_safe(">")).to_equal(62)
expect(char_code_safe("@")).to_equal(64)
```

</details>

#### uppercase letters

#### returns correct codes for A-Z range

- returns correct codes for A-Z range
- Verify: returns correct codes for A-Z range
   - Expected: char_code_safe("A") equals `65`
   - Expected: char_code_safe("M") equals `77`
   - Expected: char_code_safe("Z") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for A-Z range")
step("Verify: returns correct codes for A-Z range")
expect(char_code_safe("A")).to_equal(65)
expect(char_code_safe("M")).to_equal(77)
expect(char_code_safe("Z")).to_equal(90)
```

</details>

#### lowercase letters

#### returns correct codes for a-z range

- returns correct codes for a-z range
- Verify: returns correct codes for a-z range
   - Expected: char_code_safe("a") equals `97`
   - Expected: char_code_safe("m") equals `109`
   - Expected: char_code_safe("z") equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for a-z range")
step("Verify: returns correct codes for a-z range")
expect(char_code_safe("a")).to_equal(97)
expect(char_code_safe("m")).to_equal(109)
expect(char_code_safe("z")).to_equal(122)
```

</details>

#### bracket and brace characters

#### returns correct codes for brackets and braces

- returns correct codes for brackets and braces
- Verify: returns correct codes for brackets and braces
   - Expected: char_code_safe("[") equals `91`
   - Expected: char_code_safe("\\") equals `92`
   - Expected: char_code_safe("]") equals `93`
   - Expected: char_code_safe("^") equals `94`
   - Expected: char_code_safe("_") equals `95`
   - Expected: char_code_safe("`") equals `96`
   - Expected: char_code_safe("{") equals `123`
   - Expected: char_code_safe("|") equals `124`
   - Expected: char_code_safe("}") equals `125`
   - Expected: char_code_safe("~") equals `126`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for brackets and braces")
step("Verify: returns correct codes for brackets and braces")
expect(char_code_safe("[")).to_equal(91)
expect(char_code_safe("\\")).to_equal(92)
expect(char_code_safe("]")).to_equal(93)
expect(char_code_safe("^")).to_equal(94)
expect(char_code_safe("_")).to_equal(95)
expect(char_code_safe("`")).to_equal(96)
expect(char_code_safe("{")).to_equal(123)
expect(char_code_safe("|")).to_equal(124)
expect(char_code_safe("}")).to_equal(125)
expect(char_code_safe("~")).to_equal(126)
```

</details>

#### whitespace characters

#### returns correct codes for newline tab and carriage return

- returns correct codes for newline tab and carriage return
- Verify: returns correct codes for newline tab and carriage return
   - Expected: char_code_safe("\n") equals `10`
   - Expected: char_code_safe("\t") equals `9`
   - Expected: char_code_safe("\r") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct codes for newline tab and carriage return")
step("Verify: returns correct codes for newline tab and carriage return")
expect(char_code_safe("\n")).to_equal(10)
expect(char_code_safe("\t")).to_equal(9)
expect(char_code_safe("\r")).to_equal(13)
```

</details>

#### fallback for unknown characters

#### returns 0 for unrecognized input

- returns 0 for unrecognized input
- Verify: returns 0 for unrecognized input
   - Expected: char_code_safe("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unrecognized input")
step("Verify: returns 0 for unrecognized input")
# Empty string or non-ASCII falls through to default 0
expect(char_code_safe("")).to_equal(0)
```

</details>

### write_varint

#### when value is zero

#### returns single byte zero

- returns single byte zero
- Verify: returns single byte zero
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single byte zero")
step("Verify: returns single byte zero")
val result = write_varint(0)
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result[0]).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### when value is positive and small

#### encodes small positive as single byte

- encodes small positive as single byte
- Verify: encodes small positive as single byte
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes small positive as single byte")
step("Verify: encodes small positive as single byte")
val result = write_varint(42)
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result[0]).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### when value is positive and large

#### encodes values above 127 as multi-byte

- encodes values above 127 as multi-byte
- Verify: encodes values above 127 as multi-byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes values above 127 as multi-byte")
step("Verify: encodes values above 127 as multi-byte")
val result = write_varint(300)
expect(result.len()).to_be_greater_than(1)
```

</details>

#### when value is negative

#### prepends 255 sign marker

- prepends 255 sign marker
- Verify: prepends 255 sign marker
   - Expected: result[0] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepends 255 sign marker")
step("Verify: prepends 255 sign marker")
val result = write_varint(-42)
expect(result[0]).to_equal(255)  # oracle: 255 — named expected value from the requirement
expect(result.len()).to_be_greater_than(1)
```

</details>

### read_varint

#### roundtrip with zero

#### decodes zero correctly

- decodes zero correctly
- Verify: decodes zero correctly
   - Expected: result.0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes zero correctly")
step("Verify: decodes zero correctly")
val encoded = write_varint(0)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### roundtrip with positive

#### decodes positive correctly

- decodes positive correctly
- Verify: decodes positive correctly
   - Expected: result.0 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes positive correctly")
step("Verify: decodes positive correctly")
val encoded = write_varint(42)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### roundtrip with large positive

#### decodes multi-byte positive correctly

- decodes multi-byte positive correctly
- Verify: decodes multi-byte positive correctly
   - Expected: result.0 equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes multi-byte positive correctly")
step("Verify: decodes multi-byte positive correctly")
val encoded = write_varint(300)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(300)  # oracle: 300 — named expected value from the requirement
```

</details>

#### roundtrip with negative

#### decodes negative correctly

- decodes negative correctly
- Verify: decodes negative correctly
   - Expected: result.0 equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes negative correctly")
step("Verify: decodes negative correctly")
val encoded = write_varint(-42)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(-42)  # oracle: -42 — named expected value from the requirement
```

</details>

#### consumed bytes count

#### reports correct number of consumed bytes

- reports correct number of consumed bytes
- Verify: reports correct number of consumed bytes
   - Expected: result.1 equals `encoded.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct number of consumed bytes")
step("Verify: reports correct number of consumed bytes")
val encoded = write_varint(42)
val result = read_varint(encoded, 0)
expect(result.1).to_equal(encoded.len())
```

</details>

### serialize_int_bytes

#### starts with int type tag

- starts with int type tag
- Verify: starts with int type tag
   - Expected: result[0] equals `type_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with int type tag")
step("Verify: starts with int type tag")
val result = serialize_int_bytes(0)
expect(result[0]).to_equal(type_int())
```

</details>

#### serializes zero

- serializes zero
- Verify: serializes zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes zero")
step("Verify: serializes zero")
val result = serialize_int_bytes(0)
expect(result.len()).to_be_greater_than(1)
```

</details>

#### serializes positive integer

- serializes positive integer
- Verify: serializes positive integer
   - Expected: result[0] equals `type_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes positive integer")
step("Verify: serializes positive integer")
val result = serialize_int_bytes(100)
expect(result[0]).to_equal(type_int())
expect(result.len()).to_be_greater_than(1)
```

</details>

#### serializes negative integer

- serializes negative integer
- Verify: serializes negative integer
   - Expected: result[0] equals `type_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes negative integer")
step("Verify: serializes negative integer")
val result = serialize_int_bytes(-50)
expect(result[0]).to_equal(type_int())
```

</details>

### serialize_bool_bytes

#### serializes true with type tag and 1

- serializes true with type tag and 1
- Verify: serializes true with type tag and 1
   - Expected: result[0] equals `type_bool()`
   - Expected: result[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes true with type tag and 1")
step("Verify: serializes true with type tag and 1")
val result = serialize_bool_bytes(true)
expect(result[0]).to_equal(type_bool())
expect(result[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### serializes false with type tag and 0

- serializes false with type tag and 0
- Verify: serializes false with type tag and 0
   - Expected: result[0] equals `type_bool()`
   - Expected: result[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes false with type tag and 0")
step("Verify: serializes false with type tag and 0")
val result = serialize_bool_bytes(false)
expect(result[0]).to_equal(type_bool())
expect(result[1]).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### serialize_nil_bytes

#### returns single byte with nil type tag

- returns single byte with nil type tag
- Verify: returns single byte with nil type tag
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `type_nil()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single byte with nil type tag")
step("Verify: returns single byte with nil type tag")
val result = serialize_nil_bytes()
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result[0]).to_equal(type_nil())
```

</details>

### serialize_text_bytes

#### serializes empty string

- serializes empty string
- Verify: serializes empty string
   - Expected: result[0] equals `type_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty string")
step("Verify: serializes empty string")
val result = serialize_text_bytes("")
expect(result[0]).to_equal(type_text())
```

</details>

#### serializes non-empty string with correct length

- serializes non-empty string with correct length
- Verify: serializes non-empty string with correct length
   - Expected: result[0] equals `type_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes non-empty string with correct length")
step("Verify: serializes non-empty string with correct length")
val result = serialize_text_bytes("abc")
expect(result[0]).to_equal(type_text())
expect(result.len()).to_be_greater_than(1)
```

</details>

#### serializes string with special characters

- serializes string with special characters
- Verify: serializes string with special characters
   - Expected: result[0] equals `type_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes string with special characters")
step("Verify: serializes string with special characters")
val result = serialize_text_bytes("a\nb")
expect(result[0]).to_equal(type_text())
```

</details>

### escape_string

#### escapes double quotes

- escapes double quotes
- Verify: escapes double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes double quotes")
step("Verify: escapes double quotes")
val result = escape_string("say \"hi\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes backslashes

- escapes backslashes
- Verify: escapes backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslashes")
step("Verify: escapes backslashes")
val result = escape_string("path\\to")
expect(result).to_contain("\\\\")
```

</details>

#### escapes newlines

- escapes newlines
- Verify: escapes newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newlines")
step("Verify: escapes newlines")
val result = escape_string("a\nb")
expect(result).to_contain("\\n")
```

</details>

#### escapes tabs

- escapes tabs
- Verify: escapes tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes tabs")
step("Verify: escapes tabs")
val result = escape_string("a\tb")
expect(result).to_contain("\\t")
```

</details>

#### escapes carriage returns

- escapes carriage returns
- Verify: escapes carriage returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes carriage returns")
step("Verify: escapes carriage returns")
val result = escape_string("a\rb")
expect(result).to_contain("\\r")
```

</details>

#### passes through normal characters unchanged

- passes through normal characters unchanged
- Verify: passes through normal characters unchanged
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through normal characters unchanged")
step("Verify: passes through normal characters unchanged")
val result = escape_string("hello")
expect(result).to_equal("hello")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
val result = escape_string("")
expect(result).to_equal("")
```

</details>

### unescape_string

#### unescapes backslash-quote to quote

- unescapes backslash-quote to quote
- Verify: unescapes backslash-quote to quote


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-quote to quote")
step("Verify: unescapes backslash-quote to quote")
val result = unescape_string("say \\\"hi\\\"")
expect(result).to_contain("\"")
```

</details>

#### unescapes backslash-backslash

- unescapes backslash-backslash
- Verify: unescapes backslash-backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-backslash")
step("Verify: unescapes backslash-backslash")
val result = unescape_string("path\\\\to")
expect(result).to_contain("\\")
```

</details>

#### unescapes backslash-n to newline

- unescapes backslash-n to newline
- Verify: unescapes backslash-n to newline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-n to newline")
step("Verify: unescapes backslash-n to newline")
val result = unescape_string("a\\nb")
expect(result).to_contain("\n")
```

</details>

#### unescapes backslash-t to tab

- unescapes backslash-t to tab
- Verify: unescapes backslash-t to tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-t to tab")
step("Verify: unescapes backslash-t to tab")
val result = unescape_string("a\\tb")
expect(result).to_contain("\t")
```

</details>

#### unescapes backslash-r to carriage return

- unescapes backslash-r to carriage return
- Verify: unescapes backslash-r to carriage return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes backslash-r to carriage return")
step("Verify: unescapes backslash-r to carriage return")
val result = unescape_string("a\\rb")
expect(result).to_contain("\r")
```

</details>

#### handles unknown escape sequence

- handles unknown escape sequence
- Verify: handles unknown escape sequence
   - Expected: result equals `a\\xb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown escape sequence")
step("Verify: handles unknown escape sequence")
val result = unescape_string("a\\xb")
expect(result).to_equal("a\\xb")
```

</details>

#### handles trailing backslash at end of string

- handles trailing backslash at end of string
- Verify: handles trailing backslash at end of string
   - Expected: result equals `abc\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles trailing backslash at end of string")
step("Verify: handles trailing backslash at end of string")
val result = unescape_string("abc\\")
expect(result).to_equal("abc\\")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
val result = unescape_string("")
expect(result).to_equal("")
```

</details>

#### roundtrips with escape_string

- roundtrips with escape_string
- Verify: roundtrips with escape_string
   - Expected: roundtripped equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips with escape_string")
step("Verify: roundtrips with escape_string")
val original = "say \"hi\"\npath\\to\ttab\rreturn"
val roundtripped = unescape_string(escape_string(original))
expect(roundtripped).to_equal(original)
```

</details>

### quote_string

#### wraps string in double quotes

- wraps string in double quotes
- Verify: wraps string in double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps string in double quotes")
step("Verify: wraps string in double quotes")
val result = quote_string("hello")
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
```

</details>

#### escapes inner content

- escapes inner content
- Verify: escapes inner content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes inner content")
step("Verify: escapes inner content")
val result = quote_string("say \"hi\"")
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
expect(result).to_contain("\\\"")
```

</details>

### unquote_string

#### removes quotes and unescapes

- removes quotes and unescapes
- Verify: removes quotes and unescapes
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes quotes and unescapes")
step("Verify: removes quotes and unescapes")
val result = unquote_string("\"hello\"")
expect(result).to_equal("hello")
```

</details>

#### returns input unchanged for short strings

- returns input unchanged for short strings
- Verify: returns input unchanged for short strings
   - Expected: result equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns input unchanged for short strings")
step("Verify: returns input unchanged for short strings")
val result = unquote_string("x")
expect(result).to_equal("x")
```

</details>

#### returns input unchanged when not quoted

- returns input unchanged when not quoted
- Verify: returns input unchanged when not quoted
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns input unchanged when not quoted")
step("Verify: returns input unchanged when not quoted")
val result = unquote_string("hello")
expect(result).to_equal("hello")
```

</details>

#### returns empty input unchanged

- returns empty input unchanged
- Verify: returns empty input unchanged
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty input unchanged")
step("Verify: returns empty input unchanged")
val result = unquote_string("")
expect(result).to_equal("")
```

</details>

#### roundtrips with quote_string

- roundtrips with quote_string
- Verify: roundtrips with quote_string
   - Expected: roundtripped equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips with quote_string")
step("Verify: roundtrips with quote_string")
val original = "hello world"
val roundtripped = unquote_string(quote_string(original))
expect(roundtripped).to_equal(original)
```

</details>

### serialize_int

#### serializes positive integer

- serializes positive integer
- Verify: serializes positive integer
   - Expected: serialize_int(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes positive integer")
step("Verify: serializes positive integer")
expect(serialize_int(42)).to_equal("42")
```

</details>

#### serializes zero

- serializes zero
- Verify: serializes zero
   - Expected: serialize_int(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes zero")
step("Verify: serializes zero")
expect(serialize_int(0)).to_equal("0")
```

</details>

#### serializes negative integer

- serializes negative integer
- Verify: serializes negative integer
   - Expected: serialize_int(-7) equals `-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes negative integer")
step("Verify: serializes negative integer")
expect(serialize_int(-7)).to_equal("-7")
```

</details>

### serialize_bool

#### serializes true

- serializes true
- Verify: serializes true
   - Expected: serialize_bool(true) equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes true")
step("Verify: serializes true")
expect(serialize_bool(true)).to_equal("true")
```

</details>

#### serializes false

- serializes false
- Verify: serializes false
   - Expected: serialize_bool(false) equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes false")
step("Verify: serializes false")
expect(serialize_bool(false)).to_equal("false")
```

</details>

### serialize_nil

#### returns nil string

- returns nil string
- Verify: returns nil string
   - Expected: serialize_nil() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil string")
step("Verify: returns nil string")
expect(serialize_nil()).to_equal("nil")
```

</details>

### serialize_text

#### quotes and escapes text

- quotes and escapes text
- Verify: quotes and escapes text
   - Expected: result equals `"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes and escapes text")
step("Verify: quotes and escapes text")
val result = serialize_text("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### escapes special characters in text

- escapes special characters in text
- Verify: escapes special characters in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes special characters in text")
step("Verify: escapes special characters in text")
val result = serialize_text("a\nb")
expect(result).to_contain("\\n")
```

</details>

### serialize_list

#### serializes empty list

- serializes empty list
- Verify: serializes empty list
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty list")
step("Verify: serializes empty list")
val result = serialize_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes single-item list

- serializes single-item list
- Verify: serializes single-item list
   - Expected: result equals `[42]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes single-item list")
step("Verify: serializes single-item list")
val result = serialize_list(["42"])
expect(result).to_equal("[42]")
```

</details>

#### serializes multi-item list with commas

- serializes multi-item list with commas
- Verify: serializes multi-item list with commas
   - Expected: result equals `[1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes multi-item list with commas")
step("Verify: serializes multi-item list with commas")
val result = serialize_list(["1", "2", "3"])
expect(result).to_equal("[1, 2, 3]")
```

</details>

### serialize_tuple_text

#### serializes empty tuple

- serializes empty tuple
- Verify: serializes empty tuple
   - Expected: result equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty tuple")
step("Verify: serializes empty tuple")
val result = serialize_tuple_text([])
expect(result).to_equal("()")
```

</details>

#### serializes single-value tuple

- serializes single-value tuple
- Verify: serializes single-value tuple
   - Expected: result equals `(42)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes single-value tuple")
step("Verify: serializes single-value tuple")
val result = serialize_tuple_text(["42"])
expect(result).to_equal("(42)")
```

</details>

#### serializes multi-value tuple with commas

- serializes multi-value tuple with commas
- Verify: serializes multi-value tuple with commas
   - Expected: result equals `(1, 2, 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes multi-value tuple with commas")
step("Verify: serializes multi-value tuple with commas")
val result = serialize_tuple_text(["1", "2", "3"])
expect(result).to_equal("(1, 2, 3)")
```

</details>

### serialize_dict

#### serializes empty dict

- serializes empty dict
- Verify: serializes empty dict
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty dict")
step("Verify: serializes empty dict")
val result = serialize_dict([])
expect(result).to_equal("{}")
```

</details>

#### serializes single entry

- serializes single entry
- Verify: serializes single entry
   - Expected: result equals `{key: val}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes single entry")
step("Verify: serializes single entry")
val result = serialize_dict([("key", "val")])
expect(result).to_equal("{key: val}")
```

</details>

#### serializes multiple entries with commas

- serializes multiple entries with commas
- Verify: serializes multiple entries with commas
   - Expected: result equals `{a: 1, b: 2}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes multiple entries with commas")
step("Verify: serializes multiple entries with commas")
val result = serialize_dict([("a", "1"), ("b", "2")])
expect(result).to_equal("{a: 1, b: 2}")
```

</details>

### serialize_int_list

#### serializes empty int list

- serializes empty int list
- Verify: serializes empty int list
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty int list")
step("Verify: serializes empty int list")
val result = serialize_int_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes non-empty int list

- serializes non-empty int list
- Verify: serializes non-empty int list
   - Expected: result equals `[1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes non-empty int list")
step("Verify: serializes non-empty int list")
val result = serialize_int_list([1, 2, 3])
expect(result).to_equal("[1, 2, 3]")
```

</details>

### serialize_text_list

#### serializes empty text list

- serializes empty text list
- Verify: serializes empty text list
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty text list")
step("Verify: serializes empty text list")
val result = serialize_text_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes non-empty text list

- serializes non-empty text list
- Verify: serializes non-empty text list
   - Expected: result equals `["a", "b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes non-empty text list")
step("Verify: serializes non-empty text list")
val result = serialize_text_list(["a", "b"])
expect(result).to_equal("[\"a\", \"b\"]")
```

</details>

### serialize_bool_list

#### serializes empty bool list

- serializes empty bool list
- Verify: serializes empty bool list
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty bool list")
step("Verify: serializes empty bool list")
val result = serialize_bool_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes non-empty bool list

- serializes non-empty bool list
- Verify: serializes non-empty bool list
   - Expected: result equals `[true, false, true]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes non-empty bool list")
step("Verify: serializes non-empty bool list")
val result = serialize_bool_list([true, false, true])
expect(result).to_equal("[true, false, true]")
```

</details>

### serialize_int_list_bytes

#### starts with list type tag

- starts with list type tag
- Verify: starts with list type tag
   - Expected: result[0] equals `type_list()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with list type tag")
step("Verify: starts with list type tag")
val result = serialize_int_list_bytes([1, 2])
expect(result[0]).to_equal(type_list())
```

</details>

#### serializes empty int list

- serializes empty int list
- Verify: serializes empty int list
   - Expected: result[0] equals `type_list()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty int list")
step("Verify: serializes empty int list")
val result = serialize_int_list_bytes([])
expect(result[0]).to_equal(type_list())
```

</details>

### serialize_text_list_bytes

#### starts with list type tag

- starts with list type tag
- Verify: starts with list type tag
   - Expected: result[0] equals `type_list()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with list type tag")
step("Verify: starts with list type tag")
val result = serialize_text_list_bytes(["hello"])
expect(result[0]).to_equal(type_list())
```

</details>

#### serializes empty text list

- serializes empty text list
- Verify: serializes empty text list
   - Expected: result[0] equals `type_list()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty text list")
step("Verify: serializes empty text list")
val result = serialize_text_list_bytes([])
expect(result[0]).to_equal(type_list())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
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

- Canonical SPipe generation for source `7ede5e2ef3ddc057537dd5a91e9aa4901a2076e143818639d90d3148df653473`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ede5e2ef3ddc057537dd5a91e9aa4901a2076e143818639d90d3148df653473`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ede5e2ef3ddc057537dd5a91e9aa4901a2076e143818639d90d3148df653473`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/serialization_primitives_spec.spl
mirror: doc/06_spec/unit/lib/common/serialization_primitives_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/serialization_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/serialization_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/serialization_primitives_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 52 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/serialization_primitives_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct values for all type tags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_primitives_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct code for space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_primitives_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct code for exclamation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
