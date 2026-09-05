# HTML Entity Encoding/Decoding Specification

> Tests for `src/lib/common/html/entities.spl` covering HTML entity encoding, decoding (named and numeric), character code conversion, and helper functions. Targets 90%+ branch coverage by exercising both true and false paths of every conditional branch.

<!-- sdn-diagram:id=html_entities_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_entities_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_entities_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_entities_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/common/html_entities_coverage_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("lt")
expect(result).to_equal("<")
```

</details>

#### decodes gt to greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("gt")
expect(result).to_equal(">")
```

</details>

#### decodes amp to ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("amp")
expect(result).to_equal("&")
```

</details>

#### decodes quot to double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("quot")
expect(result).to_equal("\"")
```

</details>

#### decodes apos to apostrophe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("apos")
expect(result).to_equal("'")
```

</details>

#### whitespace and symbol entities

#### decodes nbsp to space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("nbsp")
expect(result).to_equal(" ")
```

</details>

#### decodes copy to copyright symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("copy")
expect(result).to_equal("\u00A9")
```

</details>

#### decodes reg to registered symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("reg")
expect(result).to_equal("\u00AE")
```

</details>

#### decodes trade to trademark symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("trade")
expect(result).to_equal("\u2122")
```

</details>

#### currency entities

#### decodes euro to euro sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("euro")
expect(result).to_equal("\u20AC")
```

</details>

#### decodes pound to pound sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("pound")
expect(result).to_equal("\u00A3")
```

</details>

#### decodes yen to yen sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("yen")
expect(result).to_equal("\u00A5")
```

</details>

#### decodes cent to cent sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("cent")
expect(result).to_equal("\u00A2")
```

</details>

#### typographic entities

#### decodes sect to section sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("sect")
expect(result).to_equal("\u00A7")
```

</details>

#### decodes deg to degree sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("deg")
expect(result).to_equal("\u00B0")
```

</details>

#### decodes plusmn to plus-minus sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("plusmn")
expect(result).to_equal("\u00B1")
```

</details>

#### decodes micro to micro sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("micro")
expect(result).to_equal("\u00B5")
```

</details>

#### decodes para to pilcrow sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("para")
expect(result).to_equal("\u00B6")
```

</details>

#### decodes middot to middle dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("middot")
expect(result).to_equal("\u00B7")
```

</details>

#### fraction entities

#### decodes frac14 to one quarter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("frac14")
expect(result).to_equal("\u00BC")
```

</details>

#### decodes frac12 to one half

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("frac12")
expect(result).to_equal("\u00BD")
```

</details>

#### decodes frac34 to three quarters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("frac34")
expect(result).to_equal("\u00BE")
```

</details>

#### math operator entities

#### decodes times to multiplication sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("times")
expect(result).to_equal("\u00D7")
```

</details>

#### decodes divide to division sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("divide")
expect(result).to_equal("\u00F7")
```

</details>

#### card suit entities

#### decodes hearts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("hearts")
expect(result).to_equal("\u2665")
```

</details>

#### decodes clubs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("clubs")
expect(result).to_equal("\u2663")
```

</details>

#### decodes diams

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("diams")
expect(result).to_equal("\u2666")
```

</details>

#### decodes spades

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("spades")
expect(result).to_equal("\u2660")
```

</details>

#### unknown named entities

#### returns unknown entity unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("unknown")
expect(result).to_equal("unknown")
```

</details>

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("")
expect(result).to_equal("")
```

</details>

#### returns random text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("foobar")
expect(result).to_equal("foobar")
```

</details>

#### numeric decimal entities

#### decodes decimal entity for capital A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#65")
expect(result).to_equal("A")
```

</details>

#### decodes decimal entity for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#32")
expect(result).to_equal(" ")
```

</details>

#### decodes decimal entity for exclamation mark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#33")
expect(result).to_equal("!")
```

</details>

#### decodes decimal entity for digit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#48")
expect(result).to_equal("0")
```

</details>

#### decodes decimal entity for digit 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#57")
expect(result).to_equal("9")
```

</details>

#### decodes decimal entity for lowercase a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#97")
expect(result).to_equal("a")
```

</details>

#### decodes decimal entity for lowercase z

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#122")
expect(result).to_equal("z")
```

</details>

#### decodes decimal entity for Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#90")
expect(result).to_equal("Z")
```

</details>

#### numeric entity edge cases

#### returns entity unchanged for code 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#0")
expect(result).to_equal("#0")
```

</details>

#### returns entity unchanged for code >= 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#200")
expect(result).to_equal("#200")
```

</details>

#### returns entity unchanged for hex prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#x41")
expect(result).to_equal("#x41")
```

</details>

#### returns entity unchanged for invalid decimal digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#abc")
expect(result).to_equal("#abc")
```

</details>

#### returns entity unchanged for mixed digits and letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#12a")
expect(result).to_equal("#12a")
```

</details>

#### handles hash with empty numeric part

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#")
expect(result).to_equal("#")
```

</details>

#### handles hash-x with empty hex part

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entity("#x")
expect(result).to_equal("#x")
```

</details>

### decode_html_entities

#### single entity decoding

#### decodes a single lt entity in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&lt;")
expect(result).to_equal("<")
```

</details>

#### decodes a single gt entity in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&gt;")
expect(result).to_equal(">")
```

</details>

#### decodes a single amp entity in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&amp;")
expect(result).to_equal("&")
```

</details>

#### multiple entities in text

#### decodes mixed text and entities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("a &lt; b &amp; c &gt; d")
expect(result).to_equal("a < b & c > d")
```

</details>

#### decodes adjacent entities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&lt;&gt;")
expect(result).to_equal("<>")
```

</details>

#### decodes entities at start and end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&lt;hello&gt;")
expect(result).to_equal("<hello>")
```

</details>

#### plain text without entities

#### returns plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("hello world")
expect(result).to_equal("hello world")
```

</details>

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("")
expect(result).to_equal("")
```

</details>

#### ampersand without semicolon

#### keeps bare ampersand as literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("a & b")
expect(result).to_equal("a & b")
```

</details>

#### keeps ampersand without closing semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&nosemicolon")
expect(result).to_equal("&nosemicolon")
```

</details>

#### numeric entities in full text

#### decodes numeric entity in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&#65;")
expect(result).to_equal("A")
```

</details>

#### decodes mixed named and numeric entities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&lt;&#65;&gt;")
expect(result).to_equal("<A>")
```

</details>

#### long non-entity after ampersand

#### stops searching after 20 characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_html_entities("&abcdefghijklmnopqrstuvwxyz")
expect(result).to_equal("&abcdefghijklmnopqrstuvwxyz")
```

</details>

### encode_html_entities

#### individual character encoding

#### encodes less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("<")
expect(result).to_equal("&lt;")
```

</details>

#### encodes greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities(">")
expect(result).to_equal("&gt;")
```

</details>

#### encodes ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("&")
expect(result).to_equal("&amp;")
```

</details>

#### encodes double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("\"")
expect(result).to_equal("&quot;")
```

</details>

#### passthrough characters

#### passes through plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("hello")
expect(result).to_equal("hello")
```

</details>

#### passes through single quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("'")
expect(result).to_equal("'")
```

</details>

#### passes through numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("12345")
expect(result).to_equal("12345")
```

</details>

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("")
expect(result).to_equal("")
```

</details>

#### mixed content encoding

#### encodes mixed HTML content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("<p>Hello & \"World\"</p>")
expect(result).to_equal("&lt;p&gt;Hello &amp; &quot;World&quot;&lt;/p&gt;")
```

</details>

#### encodes only special characters in mixed text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_html_entities("a < b > c & d")
expect(result).to_equal("a &lt; b &gt; c &amp; d")
```

</details>

#### roundtrip encoding and decoding

#### roundtrip for basic HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "<div>"
val encoded = encode_html_entities(original)
val decoded = decode_html_entities(encoded)
expect(decoded).to_equal(original)
```

</details>

#### roundtrip for ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Tom & Jerry"
val encoded = encode_html_entities(original)
val decoded = decode_html_entities(encoded)
expect(decoded).to_equal(original)
```

</details>

### text_from_char_code

#### space and punctuation (32-47)

#### converts code 32 to space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(32)).to_equal(" ")
```

</details>

#### converts code 33 to exclamation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(33)).to_equal("!")
```

</details>

#### converts code 34 to double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(34)).to_equal("\"")
```

</details>

#### converts code 35 to hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(35)).to_equal("#")
```

</details>

#### converts code 36 to dollar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(36)).to_equal("$")
```

</details>

#### converts code 37 to percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(37)).to_equal("%")
```

</details>

#### converts code 38 to ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(38)).to_equal("&")
```

</details>

#### converts code 39 to apostrophe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(39)).to_equal("'")
```

</details>

#### converts code 40 to open paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(40)).to_equal("(")
```

</details>

#### converts code 41 to close paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(41)).to_equal(")")
```

</details>

#### converts code 42 to asterisk

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(42)).to_equal("*")
```

</details>

#### converts code 43 to plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(43)).to_equal("+")
```

</details>

#### converts code 44 to comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(44)).to_equal(",")
```

</details>

#### converts code 45 to hyphen

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(45)).to_equal("-")
```

</details>

#### converts code 46 to period

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(46)).to_equal(".")
```

</details>

#### converts code 47 to forward slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(47)).to_equal("/")
```

</details>

#### digit range (48-57)

#### converts code 48 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(48)).to_equal("0")
```

</details>

#### converts code 49 to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(49)).to_equal("1")
```

</details>

#### converts code 57 to 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(57)).to_equal("9")
```

</details>

#### punctuation between digits and uppercase (58-64)

#### converts code 58 to colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(58)).to_equal(":")
```

</details>

#### converts code 59 to semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(59)).to_equal(";")
```

</details>

#### converts code 60 to less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(60)).to_equal("<")
```

</details>

#### converts code 61 to equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(61)).to_equal("=")
```

</details>

#### converts code 62 to greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(62)).to_equal(">")
```

</details>

#### converts code 63 to question mark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(63)).to_equal("?")
```

</details>

#### converts code 64 to at sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(64)).to_equal("@")
```

</details>

#### uppercase letters (65-90)

#### converts code 65 to A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(65)).to_equal("A")
```

</details>

#### converts code 77 to M

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(77)).to_equal("M")
```

</details>

#### converts code 90 to Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(90)).to_equal("Z")
```

</details>

#### lowercase letters (97-122)

#### converts code 97 to a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(97)).to_equal("a")
```

</details>

#### converts code 109 to m

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(109)).to_equal("m")
```

</details>

#### converts code 122 to z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(122)).to_equal("z")
```

</details>

#### out of range codes

#### returns empty for code 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(0)).to_equal("")
```

</details>

#### returns empty for code 31 (below space)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(31)).to_equal("")
```

</details>

#### returns empty for code 128 (above ASCII)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_char_code(128)).to_equal("")
```

</details>

### text_from_digit

#### all digits

#### converts 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(0)).to_equal("0")
```

</details>

#### converts 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(1)).to_equal("1")
```

</details>

#### converts 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(2)).to_equal("2")
```

</details>

#### converts 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(3)).to_equal("3")
```

</details>

#### converts 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(4)).to_equal("4")
```

</details>

#### converts 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(5)).to_equal("5")
```

</details>

#### converts 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(6)).to_equal("6")
```

</details>

#### converts 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(7)).to_equal("7")
```

</details>

#### converts 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(8)).to_equal("8")
```

</details>

#### converts 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(9)).to_equal("9")
```

</details>

#### out of range

#### returns empty for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(-1)).to_equal("")
```

</details>

#### returns empty for 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_digit(10)).to_equal("")
```

</details>

### text_from_upper

#### all uppercase letters

#### converts 0 to A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(0)).to_equal("A")
```

</details>

#### converts 1 to B

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(1)).to_equal("B")
```

</details>

#### converts 12 to M

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(12)).to_equal("M")
```

</details>

#### converts 24 to Y

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(24)).to_equal("Y")
```

</details>

#### converts 25 to Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(25)).to_equal("Z")
```

</details>

#### out of range

#### returns empty for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(-1)).to_equal("")
```

</details>

#### returns empty for 26

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_upper(26)).to_equal("")
```

</details>

### text_from_lower

#### all lowercase letters

#### converts 0 to a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(0)).to_equal("a")
```

</details>

#### converts 1 to b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(1)).to_equal("b")
```

</details>

#### converts 12 to m

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(12)).to_equal("m")
```

</details>

#### converts 24 to y

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(24)).to_equal("y")
```

</details>

#### converts 25 to z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(25)).to_equal("z")
```

</details>

#### out of range

#### returns empty for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(-1)).to_equal("")
```

</details>

#### returns empty for 26

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_lower(26)).to_equal("")
```

</details>

### is_digit

#### digit characters

#### returns true for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("0")).to_equal(true)
```

</details>

#### returns true for 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("5")).to_equal(true)
```

</details>

#### returns true for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("9")).to_equal(true)
```

</details>

#### non-digit characters

#### returns false for letter a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("a")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit(" ")).to_equal(false)
```

</details>

#### returns false for special character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("!")).to_equal(false)
```

</details>

#### returns false for slash (code 47, just below 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("/")).to_equal(false)
```

</details>

#### returns false for colon (code 58, just above 9)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
