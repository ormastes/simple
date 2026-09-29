# HTML Entity Encoding/Decoding Specification

> Tests for `src/lib/common/html/entities.spl` covering HTML entity encoding, decoding (named and numeric), character code conversion, and helper functions. Targets 90%+ branch coverage by exercising both true and false paths of every conditional branch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 140 | 140 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Entity Encoding/Decoding Specification

Tests for `src/lib/common/html/entities.spl` covering HTML entity encoding, decoding (named and numeric), character code conversion, and helper functions. Targets 90%+ branch coverage by exercising both true and false paths of every conditional branch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-HTML-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/lib/common/html_entities_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `src/lib/common/html/entities.spl` covering HTML entity encoding,
decoding (named and numeric), character code conversion, and helper functions.
Targets 90%+ branch coverage by exercising both true and false paths of every
conditional branch.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Named entity | Entities like `&lt;`, `&amp;`, `&copy;` |
| Numeric entity | Decimal `&#65;` or hex `&#x41;` |
| Encoding | Converting `<`, `>`, `&`, `"` to entity references |
| Decoding | Converting entity references back to characters |

## Related Specifications

- [HTML Parser](parser.md) - Uses decode_html_entities
- [HTML Serializer](serializer.md) - Uses encode_html_entities

## Scenarios

### decode_html_entity

#### basic HTML entities

#### decodes lt to less-than

- decodes lt to less-than
   - Expected: result equals `<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes lt to less-than")
val result = decode_html_entity("lt")
expect(result).to_equal("<")
```

</details>

#### decodes gt to greater-than

- decodes gt to greater-than
   - Expected: result equals `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes gt to greater-than")
val result = decode_html_entity("gt")
expect(result).to_equal(">")
```

</details>

#### decodes amp to ampersand

- decodes amp to ampersand
   - Expected: result equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes amp to ampersand")
val result = decode_html_entity("amp")
expect(result).to_equal("&")
```

</details>

#### decodes quot to double quote

- decodes quot to double quote
   - Expected: result equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes quot to double quote")
val result = decode_html_entity("quot")
expect(result).to_equal("\"")
```

</details>

#### decodes apos to apostrophe

- decodes apos to apostrophe
   - Expected: result equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes apos to apostrophe")
val result = decode_html_entity("apos")
expect(result).to_equal("'")
```

</details>

#### whitespace and symbol entities

#### decodes nbsp to space

- decodes nbsp to space
   - Expected: result equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes nbsp to space")
val result = decode_html_entity("nbsp")
expect(result).to_equal(" ")
```

</details>

#### decodes copy to copyright symbol

- decodes copy to copyright symbol
   - Expected: result equals `\u00A9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes copy to copyright symbol")
val result = decode_html_entity("copy")
expect(result).to_equal("\u00A9")
```

</details>

#### decodes reg to registered symbol

- decodes reg to registered symbol
   - Expected: result equals `\u00AE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes reg to registered symbol")
val result = decode_html_entity("reg")
expect(result).to_equal("\u00AE")
```

</details>

#### decodes trade to trademark symbol

- decodes trade to trademark symbol
   - Expected: result equals `\u2122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes trade to trademark symbol")
val result = decode_html_entity("trade")
expect(result).to_equal("\u2122")
```

</details>

#### currency entities

#### decodes euro to euro sign

- decodes euro to euro sign
   - Expected: result equals `\u20AC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes euro to euro sign")
val result = decode_html_entity("euro")
expect(result).to_equal("\u20AC")
```

</details>

#### decodes pound to pound sign

- decodes pound to pound sign
   - Expected: result equals `\u00A3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes pound to pound sign")
val result = decode_html_entity("pound")
expect(result).to_equal("\u00A3")
```

</details>

#### decodes yen to yen sign

- decodes yen to yen sign
   - Expected: result equals `\u00A5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes yen to yen sign")
val result = decode_html_entity("yen")
expect(result).to_equal("\u00A5")
```

</details>

#### decodes cent to cent sign

- decodes cent to cent sign
   - Expected: result equals `\u00A2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes cent to cent sign")
val result = decode_html_entity("cent")
expect(result).to_equal("\u00A2")
```

</details>

#### typographic entities

#### decodes sect to section sign

- decodes sect to section sign
   - Expected: result equals `\u00A7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes sect to section sign")
val result = decode_html_entity("sect")
expect(result).to_equal("\u00A7")
```

</details>

#### decodes deg to degree sign

- decodes deg to degree sign
   - Expected: result equals `\u00B0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes deg to degree sign")
val result = decode_html_entity("deg")
expect(result).to_equal("\u00B0")
```

</details>

#### decodes plusmn to plus-minus sign

- decodes plusmn to plus-minus sign
   - Expected: result equals `\u00B1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes plusmn to plus-minus sign")
val result = decode_html_entity("plusmn")
expect(result).to_equal("\u00B1")
```

</details>

#### decodes micro to micro sign

- decodes micro to micro sign
   - Expected: result equals `\u00B5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes micro to micro sign")
val result = decode_html_entity("micro")
expect(result).to_equal("\u00B5")
```

</details>

#### decodes para to pilcrow sign

- decodes para to pilcrow sign
   - Expected: result equals `\u00B6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes para to pilcrow sign")
val result = decode_html_entity("para")
expect(result).to_equal("\u00B6")
```

</details>

#### decodes middot to middle dot

- decodes middot to middle dot
   - Expected: result equals `\u00B7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes middot to middle dot")
val result = decode_html_entity("middot")
expect(result).to_equal("\u00B7")
```

</details>

#### fraction entities

#### decodes frac14 to one quarter

- decodes frac14 to one quarter
   - Expected: result equals `\u00BC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes frac14 to one quarter")
val result = decode_html_entity("frac14")
expect(result).to_equal("\u00BC")
```

</details>

#### decodes frac12 to one half

- decodes frac12 to one half
   - Expected: result equals `\u00BD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes frac12 to one half")
val result = decode_html_entity("frac12")
expect(result).to_equal("\u00BD")
```

</details>

#### decodes frac34 to three quarters

- decodes frac34 to three quarters
   - Expected: result equals `\u00BE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes frac34 to three quarters")
val result = decode_html_entity("frac34")
expect(result).to_equal("\u00BE")
```

</details>

#### math operator entities

#### decodes times to multiplication sign

- decodes times to multiplication sign
   - Expected: result equals `\u00D7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes times to multiplication sign")
val result = decode_html_entity("times")
expect(result).to_equal("\u00D7")
```

</details>

#### decodes divide to division sign

- decodes divide to division sign
   - Expected: result equals `\u00F7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes divide to division sign")
val result = decode_html_entity("divide")
expect(result).to_equal("\u00F7")
```

</details>

#### card suit entities

#### decodes hearts

- decodes hearts
   - Expected: result equals `\u2665`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes hearts")
val result = decode_html_entity("hearts")
expect(result).to_equal("\u2665")
```

</details>

#### decodes clubs

- decodes clubs
   - Expected: result equals `\u2663`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes clubs")
val result = decode_html_entity("clubs")
expect(result).to_equal("\u2663")
```

</details>

#### decodes diams

- decodes diams
   - Expected: result equals `\u2666`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes diams")
val result = decode_html_entity("diams")
expect(result).to_equal("\u2666")
```

</details>

#### decodes spades

- decodes spades
   - Expected: result equals `\u2660`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes spades")
val result = decode_html_entity("spades")
expect(result).to_equal("\u2660")
```

</details>

#### unknown named entities

#### returns unknown entity unchanged

- returns unknown entity unchanged
   - Expected: result equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown entity unchanged")
val result = decode_html_entity("unknown")
expect(result).to_equal("unknown")
```

</details>

#### returns empty string unchanged

- returns empty string unchanged
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string unchanged")
val result = decode_html_entity("")
expect(result).to_equal("")
```

</details>

#### returns random text unchanged

- returns random text unchanged
   - Expected: result equals `foobar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns random text unchanged")
val result = decode_html_entity("foobar")
expect(result).to_equal("foobar")
```

</details>

#### numeric decimal entities

#### decodes decimal entity for capital A

- decodes decimal entity for capital A
   - Expected: result equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for capital A")
val result = decode_html_entity("#65")
expect(result).to_equal("A")
```

</details>

#### decodes decimal entity for space

- decodes decimal entity for space
   - Expected: result equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for space")
val result = decode_html_entity("#32")
expect(result).to_equal(" ")
```

</details>

#### decodes decimal entity for exclamation mark

- decodes decimal entity for exclamation mark
   - Expected: result equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for exclamation mark")
val result = decode_html_entity("#33")
expect(result).to_equal("!")
```

</details>

#### decodes decimal entity for digit 0

- decodes decimal entity for digit 0
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for digit 0")
val result = decode_html_entity("#48")
expect(result).to_equal("0")
```

</details>

#### decodes decimal entity for digit 9

- decodes decimal entity for digit 9
   - Expected: result equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for digit 9")
val result = decode_html_entity("#57")
expect(result).to_equal("9")
```

</details>

#### decodes decimal entity for lowercase a

- decodes decimal entity for lowercase a
   - Expected: result equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for lowercase a")
val result = decode_html_entity("#97")
expect(result).to_equal("a")
```

</details>

#### decodes decimal entity for lowercase z

- decodes decimal entity for lowercase z
   - Expected: result equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for lowercase z")
val result = decode_html_entity("#122")
expect(result).to_equal("z")
```

</details>

#### decodes decimal entity for Z

- decodes decimal entity for Z
   - Expected: result equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes decimal entity for Z")
val result = decode_html_entity("#90")
expect(result).to_equal("Z")
```

</details>

#### numeric entity edge cases

#### returns entity unchanged for code 0

- returns entity unchanged for code 0
   - Expected: result equals `#0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entity unchanged for code 0")
"""
When the parsed code is 0, the `code > 0` branch is false,
so the entity is returned unchanged.
"""
val result = decode_html_entity("#0")
expect(result).to_equal("#0")
```

</details>

#### returns entity unchanged for code >= 128

- returns entity unchanged for code >= 128
   - Expected: result equals `#200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entity unchanged for code >= 128")
"""
When the parsed code is >= 128, the `code < 128` branch is false,
so the entity is returned unchanged.
"""
val result = decode_html_entity("#200")
expect(result).to_equal("#200")
```

</details>

#### returns entity unchanged for hex prefix

- returns entity unchanged for hex prefix
   - Expected: result equals `#x41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entity unchanged for hex prefix")
"""
Hex entities like `#x41` are not fully supported, so the
`is_hex` branch returns the entity unchanged.
"""
val result = decode_html_entity("#x41")
expect(result).to_equal("#x41")
```

</details>

#### returns entity unchanged for invalid decimal digits

- returns entity unchanged for invalid decimal digits
   - Expected: result equals `#abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entity unchanged for invalid decimal digits")
"""
When a non-digit character is encountered, `valid` becomes false
and the entity is returned unchanged.
"""
val result = decode_html_entity("#abc")
expect(result).to_equal("#abc")
```

</details>

#### returns entity unchanged for mixed digits and letters

- returns entity unchanged for mixed digits and letters
   - Expected: result equals `#12a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entity unchanged for mixed digits and letters")
val result = decode_html_entity("#12a")
expect(result).to_equal("#12a")
```

</details>

#### handles hash with empty numeric part

- handles hash with empty numeric part
   - Expected: result equals `#`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles hash with empty numeric part")
"""
When `#` is followed by nothing, `num_part.length() > 0` is false,
so the entity is returned unchanged.
"""
val result = decode_html_entity("#")
expect(result).to_equal("#")
```

</details>

#### handles hash-x with empty hex part

- handles hash-x with empty hex part
   - Expected: result equals `#x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles hash-x with empty hex part")
"""
When `#x` is followed by nothing, `final_num.length() > 0` is false,
so the entity is returned unchanged.
"""
val result = decode_html_entity("#x")
expect(result).to_equal("#x")
```

</details>

### decode_html_entities

#### single entity decoding

#### decodes a single lt entity in text

- decodes a single lt entity in text
   - Expected: result equals `<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a single lt entity in text")
val result = decode_html_entities("&lt;")
expect(result).to_equal("<")
```

</details>

#### decodes a single gt entity in text

- decodes a single gt entity in text
   - Expected: result equals `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a single gt entity in text")
val result = decode_html_entities("&gt;")
expect(result).to_equal(">")
```

</details>

#### decodes a single amp entity in text

- decodes a single amp entity in text
   - Expected: result equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a single amp entity in text")
val result = decode_html_entities("&amp;")
expect(result).to_equal("&")
```

</details>

#### multiple entities in text

#### decodes mixed text and entities

- decodes mixed text and entities
   - Expected: result equals `a < b & c > d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes mixed text and entities")
val result = decode_html_entities("a &lt; b &amp; c &gt; d")
expect(result).to_equal("a < b & c > d")
```

</details>

#### decodes adjacent entities

- decodes adjacent entities
   - Expected: result equals `<>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes adjacent entities")
val result = decode_html_entities("&lt;&gt;")
expect(result).to_equal("<>")
```

</details>

#### decodes entities at start and end

- decodes entities at start and end
   - Expected: result equals `<hello>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes entities at start and end")
val result = decode_html_entities("&lt;hello&gt;")
expect(result).to_equal("<hello>")
```

</details>

#### plain text without entities

#### returns plain text unchanged

- returns plain text unchanged
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns plain text unchanged")
val result = decode_html_entities("hello world")
expect(result).to_equal("hello world")
```

</details>

#### returns empty string unchanged

- returns empty string unchanged
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string unchanged")
val result = decode_html_entities("")
expect(result).to_equal("")
```

</details>

#### ampersand without semicolon

#### keeps bare ampersand as literal

- keeps bare ampersand as literal
   - Expected: result equals `a & b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bare ampersand as literal")
val result = decode_html_entities("a & b")
expect(result).to_equal("a & b")
```

</details>

#### keeps ampersand without closing semicolon

- keeps ampersand without closing semicolon
   - Expected: result equals `&nosemicolon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ampersand without closing semicolon")
val result = decode_html_entities("&nosemicolon")
expect(result).to_equal("&nosemicolon")
```

</details>

#### numeric entities in full text

#### decodes numeric entity in text

- decodes numeric entity in text
   - Expected: result equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes numeric entity in text")
val result = decode_html_entities("&#65;")
expect(result).to_equal("A")
```

</details>

#### decodes mixed named and numeric entities

- decodes mixed named and numeric entities
   - Expected: result equals `<A>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes mixed named and numeric entities")
val result = decode_html_entities("&lt;&#65;&gt;")
expect(result).to_equal("<A>")
```

</details>

#### long non-entity after ampersand

#### stops searching after 20 characters

- stops searching after 20 characters
   - Expected: result equals `&abcdefghijklmnopqrstuvwxyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops searching after 20 characters")
val result = decode_html_entities("&abcdefghijklmnopqrstuvwxyz")
expect(result).to_equal("&abcdefghijklmnopqrstuvwxyz")
```

</details>

### encode_html_entities

#### individual character encoding

#### encodes less-than

- encodes less-than
   - Expected: result equals `&lt;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes less-than")
val result = encode_html_entities("<")
expect(result).to_equal("&lt;")
```

</details>

#### encodes greater-than

- encodes greater-than
   - Expected: result equals `&gt;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes greater-than")
val result = encode_html_entities(">")
expect(result).to_equal("&gt;")
```

</details>

#### encodes ampersand

- encodes ampersand
   - Expected: result equals `&amp;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes ampersand")
val result = encode_html_entities("&")
expect(result).to_equal("&amp;")
```

</details>

#### encodes double quote

- encodes double quote
   - Expected: result equals `&quot;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes double quote")
val result = encode_html_entities("\"")
expect(result).to_equal("&quot;")
```

</details>

#### passthrough characters

#### passes through plain text

- passes through plain text
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through plain text")
val result = encode_html_entities("hello")
expect(result).to_equal("hello")
```

</details>

#### passes through single quote

- passes through single quote
   - Expected: result equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through single quote")
val result = encode_html_entities("'")
expect(result).to_equal("'")
```

</details>

#### passes through numbers

- passes through numbers
   - Expected: result equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through numbers")
val result = encode_html_entities("12345")
expect(result).to_equal("12345")
```

</details>

#### returns empty string unchanged

- returns empty string unchanged
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string unchanged")
val result = encode_html_entities("")
expect(result).to_equal("")
```

</details>

#### mixed content encoding

#### encodes mixed HTML content

- encodes mixed HTML content
   - Expected: result equals `&lt;p&gt;Hello &amp; &quot;World&quot;&lt;/p&gt;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes mixed HTML content")
val result = encode_html_entities("<p>Hello & \"World\"</p>")
expect(result).to_equal("&lt;p&gt;Hello &amp; &quot;World&quot;&lt;/p&gt;")
```

</details>

#### encodes only special characters in mixed text

- encodes only special characters in mixed text
   - Expected: result equals `a &lt; b &gt; c &amp; d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes only special characters in mixed text")
val result = encode_html_entities("a < b > c & d")
expect(result).to_equal("a &lt; b &gt; c &amp; d")
```

</details>

#### roundtrip encoding and decoding

#### roundtrip for basic HTML

- roundtrip for basic HTML
   - Expected: decoded equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrip for basic HTML")
val original = "<div>"
val encoded = encode_html_entities(original)
val decoded = decode_html_entities(encoded)
expect(decoded).to_equal(original)
```

</details>

#### roundtrip for ampersand

- roundtrip for ampersand
   - Expected: decoded equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrip for ampersand")
val original = "Tom & Jerry"
val encoded = encode_html_entities(original)
val decoded = decode_html_entities(encoded)
expect(decoded).to_equal(original)
```

</details>

### text_from_char_code

#### space and punctuation (32-47)

#### converts code 32 to space

- converts code 32 to space
   - Expected: text_from_char_code(32) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 32 to space")
expect(text_from_char_code(32)).to_equal(" ")
```

</details>

#### converts code 33 to exclamation

- converts code 33 to exclamation
   - Expected: text_from_char_code(33) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 33 to exclamation")
expect(text_from_char_code(33)).to_equal("!")
```

</details>

#### converts code 34 to double quote

- converts code 34 to double quote
   - Expected: text_from_char_code(34) equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 34 to double quote")
expect(text_from_char_code(34)).to_equal("\"")
```

</details>

#### converts code 35 to hash

- converts code 35 to hash
   - Expected: text_from_char_code(35) equals `#`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 35 to hash")
expect(text_from_char_code(35)).to_equal("#")
```

</details>

#### converts code 36 to dollar

- converts code 36 to dollar
   - Expected: text_from_char_code(36) equals `$`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 36 to dollar")
expect(text_from_char_code(36)).to_equal("$")
```

</details>

#### converts code 37 to percent

- converts code 37 to percent
   - Expected: text_from_char_code(37) equals `%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 37 to percent")
expect(text_from_char_code(37)).to_equal("%")
```

</details>

#### converts code 38 to ampersand

- converts code 38 to ampersand
   - Expected: text_from_char_code(38) equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 38 to ampersand")
expect(text_from_char_code(38)).to_equal("&")
```

</details>

#### converts code 39 to apostrophe

- converts code 39 to apostrophe
   - Expected: text_from_char_code(39) equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 39 to apostrophe")
expect(text_from_char_code(39)).to_equal("'")
```

</details>

#### converts code 40 to open paren

- converts code 40 to open paren
   - Expected: text_from_char_code(40) equals `(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 40 to open paren")
expect(text_from_char_code(40)).to_equal("(")
```

</details>

#### converts code 41 to close paren

- converts code 41 to close paren
   - Expected: text_from_char_code(41) equals `)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 41 to close paren")
expect(text_from_char_code(41)).to_equal(")")
```

</details>

#### converts code 42 to asterisk

- converts code 42 to asterisk
   - Expected: text_from_char_code(42) equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 42 to asterisk")
expect(text_from_char_code(42)).to_equal("*")
```

</details>

#### converts code 43 to plus

- converts code 43 to plus
   - Expected: text_from_char_code(43) equals `+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 43 to plus")
expect(text_from_char_code(43)).to_equal("+")
```

</details>

#### converts code 44 to comma

- converts code 44 to comma
   - Expected: text_from_char_code(44) equals `,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 44 to comma")
expect(text_from_char_code(44)).to_equal(",")
```

</details>

#### converts code 45 to hyphen

- converts code 45 to hyphen
   - Expected: text_from_char_code(45) equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 45 to hyphen")
expect(text_from_char_code(45)).to_equal("-")
```

</details>

#### converts code 46 to period

- converts code 46 to period
   - Expected: text_from_char_code(46) equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 46 to period")
expect(text_from_char_code(46)).to_equal(".")
```

</details>

#### converts code 47 to forward slash

- converts code 47 to forward slash
   - Expected: text_from_char_code(47) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 47 to forward slash")
expect(text_from_char_code(47)).to_equal("/")
```

</details>

#### digit range (48-57)

#### converts code 48 to 0

- converts code 48 to 0
   - Expected: text_from_char_code(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 48 to 0")
expect(text_from_char_code(48)).to_equal("0")
```

</details>

#### converts code 49 to 1

- converts code 49 to 1
   - Expected: text_from_char_code(49) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 49 to 1")
expect(text_from_char_code(49)).to_equal("1")
```

</details>

#### converts code 57 to 9

- converts code 57 to 9
   - Expected: text_from_char_code(57) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 57 to 9")
expect(text_from_char_code(57)).to_equal("9")
```

</details>

#### punctuation between digits and uppercase (58-64)

#### converts code 58 to colon

- converts code 58 to colon
   - Expected: text_from_char_code(58) equals `:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 58 to colon")
expect(text_from_char_code(58)).to_equal(":")
```

</details>

#### converts code 59 to semicolon

- converts code 59 to semicolon
   - Expected: text_from_char_code(59) equals `;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 59 to semicolon")
expect(text_from_char_code(59)).to_equal(";")
```

</details>

#### converts code 60 to less-than

- converts code 60 to less-than
   - Expected: text_from_char_code(60) equals `<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 60 to less-than")
expect(text_from_char_code(60)).to_equal("<")
```

</details>

#### converts code 61 to equals

- converts code 61 to equals
   - Expected: text_from_char_code(61) equals `=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 61 to equals")
expect(text_from_char_code(61)).to_equal("=")
```

</details>

#### converts code 62 to greater-than

- converts code 62 to greater-than
   - Expected: text_from_char_code(62) equals `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 62 to greater-than")
expect(text_from_char_code(62)).to_equal(">")
```

</details>

#### converts code 63 to question mark

- converts code 63 to question mark
   - Expected: text_from_char_code(63) equals `?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 63 to question mark")
expect(text_from_char_code(63)).to_equal("?")
```

</details>

#### converts code 64 to at sign

- converts code 64 to at sign
   - Expected: text_from_char_code(64) equals `@`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 64 to at sign")
expect(text_from_char_code(64)).to_equal("@")
```

</details>

#### uppercase letters (65-90)

#### converts code 65 to A

- converts code 65 to A
   - Expected: text_from_char_code(65) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 65 to A")
expect(text_from_char_code(65)).to_equal("A")
```

</details>

#### converts code 77 to M

- converts code 77 to M
   - Expected: text_from_char_code(77) equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 77 to M")
expect(text_from_char_code(77)).to_equal("M")
```

</details>

#### converts code 90 to Z

- converts code 90 to Z
   - Expected: text_from_char_code(90) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 90 to Z")
expect(text_from_char_code(90)).to_equal("Z")
```

</details>

#### lowercase letters (97-122)

#### converts code 97 to a

- converts code 97 to a
   - Expected: text_from_char_code(97) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 97 to a")
expect(text_from_char_code(97)).to_equal("a")
```

</details>

#### converts code 109 to m

- converts code 109 to m
   - Expected: text_from_char_code(109) equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 109 to m")
expect(text_from_char_code(109)).to_equal("m")
```

</details>

#### converts code 122 to z

- converts code 122 to z
   - Expected: text_from_char_code(122) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code 122 to z")
expect(text_from_char_code(122)).to_equal("z")
```

</details>

#### out of range codes

#### returns empty for code 0

- returns empty for code 0
   - Expected: text_from_char_code(0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for code 0")
expect(text_from_char_code(0)).to_equal("")
```

</details>

#### returns empty for code 31 (below space)

- returns empty for code 31 (below space)
   - Expected: text_from_char_code(31) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for code 31 (below space)")
expect(text_from_char_code(31)).to_equal("")
```

</details>

#### returns empty for code 128 (above ASCII)

- returns empty for code 128 (above ASCII)
   - Expected: text_from_char_code(128) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for code 128 (above ASCII)")
expect(text_from_char_code(128)).to_equal("")
```

</details>

### text_from_digit

#### all digits

#### converts 0

- converts 0
   - Expected: text_from_digit(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 0")
expect(text_from_digit(0)).to_equal("0")
```

</details>

#### converts 1

- converts 1
   - Expected: text_from_digit(1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 1")
expect(text_from_digit(1)).to_equal("1")
```

</details>

#### converts 2

- converts 2
   - Expected: text_from_digit(2) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 2")
expect(text_from_digit(2)).to_equal("2")
```

</details>

#### converts 3

- converts 3
   - Expected: text_from_digit(3) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 3")
expect(text_from_digit(3)).to_equal("3")
```

</details>

#### converts 4

- converts 4
   - Expected: text_from_digit(4) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 4")
expect(text_from_digit(4)).to_equal("4")
```

</details>

#### converts 5

- converts 5
   - Expected: text_from_digit(5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 5")
expect(text_from_digit(5)).to_equal("5")
```

</details>

#### converts 6

- converts 6
   - Expected: text_from_digit(6) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 6")
expect(text_from_digit(6)).to_equal("6")
```

</details>

#### converts 7

- converts 7
   - Expected: text_from_digit(7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 7")
expect(text_from_digit(7)).to_equal("7")
```

</details>

#### converts 8

- converts 8
   - Expected: text_from_digit(8) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 8")
expect(text_from_digit(8)).to_equal("8")
```

</details>

#### converts 9

- converts 9
   - Expected: text_from_digit(9) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 9")
expect(text_from_digit(9)).to_equal("9")
```

</details>

#### out of range

#### returns empty for negative

- returns empty for negative
   - Expected: text_from_digit(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative")
expect(text_from_digit(-1)).to_equal("")
```

</details>

#### returns empty for 10

- returns empty for 10
   - Expected: text_from_digit(10) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for 10")
expect(text_from_digit(10)).to_equal("")
```

</details>

### text_from_upper

#### all uppercase letters

#### converts 0 to A

- converts 0 to A
   - Expected: text_from_upper(0) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 0 to A")
expect(text_from_upper(0)).to_equal("A")
```

</details>

#### converts 1 to B

- converts 1 to B
   - Expected: text_from_upper(1) equals `B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 1 to B")
expect(text_from_upper(1)).to_equal("B")
```

</details>

#### converts 12 to M

- converts 12 to M
   - Expected: text_from_upper(12) equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 12 to M")
expect(text_from_upper(12)).to_equal("M")
```

</details>

#### converts 24 to Y

- converts 24 to Y
   - Expected: text_from_upper(24) equals `Y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 24 to Y")
expect(text_from_upper(24)).to_equal("Y")
```

</details>

#### converts 25 to Z

- converts 25 to Z
   - Expected: text_from_upper(25) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 25 to Z")
expect(text_from_upper(25)).to_equal("Z")
```

</details>

#### out of range

#### returns empty for negative

- returns empty for negative
   - Expected: text_from_upper(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative")
expect(text_from_upper(-1)).to_equal("")
```

</details>

#### returns empty for 26

- returns empty for 26
   - Expected: text_from_upper(26) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for 26")
expect(text_from_upper(26)).to_equal("")
```

</details>

### text_from_lower

#### all lowercase letters

#### converts 0 to a

- converts 0 to a
   - Expected: text_from_lower(0) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 0 to a")
expect(text_from_lower(0)).to_equal("a")
```

</details>

#### converts 1 to b

- converts 1 to b
   - Expected: text_from_lower(1) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 1 to b")
expect(text_from_lower(1)).to_equal("b")
```

</details>

#### converts 12 to m

- converts 12 to m
   - Expected: text_from_lower(12) equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 12 to m")
expect(text_from_lower(12)).to_equal("m")
```

</details>

#### converts 24 to y

- converts 24 to y
   - Expected: text_from_lower(24) equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 24 to y")
expect(text_from_lower(24)).to_equal("y")
```

</details>

#### converts 25 to z

- converts 25 to z
   - Expected: text_from_lower(25) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 25 to z")
expect(text_from_lower(25)).to_equal("z")
```

</details>

#### out of range

#### returns empty for negative

- returns empty for negative
   - Expected: text_from_lower(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative")
expect(text_from_lower(-1)).to_equal("")
```

</details>

#### returns empty for 26

- returns empty for 26
   - Expected: text_from_lower(26) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for 26")
expect(text_from_lower(26)).to_equal("")
```

</details>

### is_digit

#### digit characters

#### returns true for 0

- returns true for 0
   - Expected: is_digit("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 0")
expect(is_digit("0")).to_equal(true)
```

</details>

#### returns true for 5

- returns true for 5
   - Expected: is_digit("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 5")
expect(is_digit("5")).to_equal(true)
```

</details>

#### returns true for 9

- returns true for 9
   - Expected: is_digit("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 9")
expect(is_digit("9")).to_equal(true)
```

</details>

#### non-digit characters

#### returns false for letter a

- returns false for letter a
   - Expected: is_digit("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for letter a")
expect(is_digit("a")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
   - Expected: is_digit(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
expect(is_digit(" ")).to_equal(false)
```

</details>

#### returns false for special character

- returns false for special character
   - Expected: is_digit("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for special character")
expect(is_digit("!")).to_equal(false)
```

</details>

#### returns false for slash (code 47, just below 0)

- returns false for slash (code 47, just below 0)
   - Expected: is_digit("/") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for slash (code 47, just below 0)")
expect(is_digit("/")).to_equal(false)
```

</details>

#### returns false for colon (code 58, just above 9)

- returns false for colon (code 58, just above 9)
   - Expected: is_digit(":") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for colon (code 58, just above 9)")
expect(is_digit(":")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 140 |
| Active scenarios | 140 |
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

- Canonical SPipe generation for source `eb19877a75e8176a167e73dce99654e182fd02ba85448332c8470e535e71cdb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb19877a75e8176a167e73dce99654e182fd02ba85448332c8470e535e71cdb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb19877a75e8176a167e73dce99654e182fd02ba85448332c8470e535e71cdb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/html_entities_coverage_spec.spl
mirror: doc/06_spec/unit/lib/common/html_entities_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/html_entities_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/html_entities_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/html_entities_coverage_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes lt to less-than' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/html_entities_coverage_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes gt to greater-than' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/html_entities_coverage_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes amp to ampersand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
