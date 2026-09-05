# HTML Character References

> An HTML author writes `AT&amp;T`, `caf&#233;` or `&#x2014;` and expects every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Character References

An HTML author writes `AT&amp;T`, `caf&#233;` or `&#x2014;` and expects every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/unit/lib/common/html/character_references_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

An HTML author writes `AT&amp;T`, `caf&#233;` or `&#x2014;` and expects every
renderer in this repo to show `AT&T`, `café` and an em dash. This module is the
single place that translation happens, so a render lane imports it instead of
growing its own entity table. `blink.html_parser.tokenizer` is its first
consumer; `common.html.entities` is the older, weaker decoder it supersedes.

## Scope and Preconditions

`decode_character_references(input)` scans a whole string. `named_entity(name)`
and `numeric_entity(body)` read one reference each, and `match_entity(chars, i)`
reads one out of a codepoint array at a position.

Supported: the HTML 4 named set plus the common typographic, currency, maths,
arrow and Greek names; decimal `&#NNN;`; hexadecimal `&#xHH;` and `&#XHH;`.
Names are case-sensitive, as HTML defines them, and the terminating `;` is
required.

## Primary Workflow

A reference this module understands becomes the character it denotes. **A
reference it does not understand is reported and left exactly as the author
wrote it** — that is what this spec is really about. There are four distinct
ways to fail and each one is covered here on purpose:

| Failure | Example | Result |
|---------|---------|--------|
| Unterminated | `&amp` (no `;`) | text stays `&amp`, error recorded |
| Unknown name | `&bogus;` | text stays `&bogus;`, error recorded |
| Malformed numeric | `&#12z4;` | text stays verbatim, error recorded |
| Out-of-range numeric | `&#0;`, `&#xD800;` | text stays verbatim, error recorded |

None of them ever produces a substitute character. A decoder that guesses emits
a wrong glyph that reads as content and survives every smoke test; a decoder
that reports leaves the evidence in `errors` and the source text on screen.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `EntityMatch.ok` | false means the reference was NOT decoded; `consumed` is 0. |
| Verbatim recovery | Undecodable input is copied through byte-for-byte. |
| Windows-1252 remap | `&#128;`..`&#159;` map per WHATWG, the one specified translation. |

## Compatibility and Limitations

The semicolon-less legacy forms (`&ampX`) are treated as unterminated rather
than decoded. The named table is the common set, not the full 2231-entry WHATWG
table; a name outside it is an explicit unknown-name failure.

## Related Specifications

- [Blink HTML tokenizer entities](../../blink/html_tokenizer_entities_spec.md)

## Scenarios

### decoding a named character reference

#### reads the five references every document depends on

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the five references every document depends on
- decode the ampersand, angle brackets and both quote marks
   - Expected: decode_character_references("AT&amp;T") equals `AT&T`
   - Expected: decode_character_references("&lt;p&gt;") equals `<p>`
   - Expected: decode_character_references("&quot;x&quot;") equals `"x"`
   - Expected: decode_character_references("&apos;y&apos;") equals `'y'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the five references every document depends on")
step("decode the ampersand, angle brackets and both quote marks")
expect(decode_character_references("AT&amp;T")).to_equal("AT&T")
expect(decode_character_references("&lt;p&gt;")).to_equal("<p>")
expect(decode_character_references("&quot;x&quot;")).to_equal("\"x\"")
expect(decode_character_references("&apos;y&apos;")).to_equal("'y'")
```

</details>

#### reads a name from the wider table, not just the core five

- reads a name from the wider table, not just the core five
- decode accented Latin, currency, typographic and Greek names
   - Expected: _named("eacute") equals `é`
   - Expected: _named("euro") equals `€`
   - Expected: _named("mdash") equals `—`
   - Expected: _named("hellip") equals `…`
   - Expected: _named("nbsp") equals ` `
   - Expected: _named("omega") equals `ω`
   - Expected: _named("rarr") equals `→`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a name from the wider table, not just the core five")
step("decode accented Latin, currency, typographic and Greek names")
expect(_named("eacute")).to_equal("é")
expect(_named("euro")).to_equal("€")
expect(_named("mdash")).to_equal("—")
expect(_named("hellip")).to_equal("…")
expect(_named("nbsp")).to_equal(" ")
expect(_named("omega")).to_equal("ω")
expect(_named("rarr")).to_equal("→")
```

</details>

#### reads only the capitalisations HTML actually defines

- reads only the capitalisations HTML actually defines
- decode `&AMP;`, which HTML defines alongside `&amp;`
   - Expected: _named("AMP") equals `&`
- refuse `&Amp;`, which HTML does not define — names are case-sensitive
   - Expected: _named("Amp") equals `refused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads only the capitalisations HTML actually defines")
step("decode `&AMP;`, which HTML defines alongside `&amp;`")
expect(_named("AMP")).to_equal("&")
step("refuse `&Amp;`, which HTML does not define — names are case-sensitive")
expect(_named("Amp")).to_equal("refused")
```

</details>

#### refuses an unknown name instead of inventing a character

- refuses an unknown name instead of inventing a character
- look up a name that is not in the table
   - Expected: _named("bogus") equals `refused`
- confirm the source spelling survives in the decoded text
   - Expected: decode_character_references("a &bogus; b") equals `a &bogus; b`
- confirm the refusal was reported, not swallowed
   - Expected: _error_count("a &bogus; b") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an unknown name instead of inventing a character")
step("look up a name that is not in the table")
expect(_named("bogus")).to_equal("refused")
step("confirm the source spelling survives in the decoded text")
expect(decode_character_references("a &bogus; b")).to_equal("a &bogus; b")
step("confirm the refusal was reported, not swallowed")
expect(_error_count("a &bogus; b")).to_equal(1)
```

</details>

### decoding a numeric character reference

#### reads a decimal reference

- reads a decimal reference
- decode `&#233;` and `&#8212;`
   - Expected: decode_character_references("caf&#233;") equals `café`
   - Expected: _numeric("8212") equals `—`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a decimal reference")
step("decode `&#233;` and `&#8212;`")
expect(decode_character_references("caf&#233;")).to_equal("café")
expect(_numeric("8212")).to_equal("—")
```

</details>

#### reads a hexadecimal reference in either letter case

- reads a hexadecimal reference in either letter case
- decode `&#x2014;`, `&#X2014;` and a lowercase-digit form
   - Expected: _numeric("x2014") equals `—`
   - Expected: _numeric("X2014") equals `—`
   - Expected: _numeric("xe9") equals `é`
   - Expected: _numeric("xE9") equals `é`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a hexadecimal reference in either letter case")
step("decode `&#x2014;`, `&#X2014;` and a lowercase-digit form")
expect(_numeric("x2014")).to_equal("—")
expect(_numeric("X2014")).to_equal("—")
expect(_numeric("xe9")).to_equal("é")
expect(_numeric("xE9")).to_equal("é")
```

</details>

#### reads a decimal and a hexadecimal spelling of one character identically

- reads a decimal and a hexadecimal spelling of one character identically
- decode the em dash both ways and compare
   - Expected: _numeric("8212") equals `_numeric("x2014")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a decimal and a hexadecimal spelling of one character identically")
step("decode the em dash both ways and compare")
expect(_numeric("8212")).to_equal(_numeric("x2014"))
```

</details>

#### remaps a C1 reference to the character the author meant

- remaps a C1 reference to the character the author meant
- decode `&#151;`, which authors type meaning an em dash
   - Expected: _numeric("151") equals `—`
- decode `&#128;`, the windows-1252 euro sign
   - Expected: _numeric("128") equals `€`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remaps a C1 reference to the character the author meant")
step("decode `&#151;`, which authors type meaning an em dash")
expect(_numeric("151")).to_equal("—")
step("decode `&#128;`, the windows-1252 euro sign")
expect(_numeric("128")).to_equal("€")
```

</details>

#### refuses a malformed number instead of decoding part of it

- refuses a malformed number instead of decoding part of it
- offer a body with a non-digit in it
   - Expected: _numeric("12z4") equals `refused`
- offer a hexadecimal digit in a decimal reference
   - Expected: _numeric("1f") equals `refused`
- offer a reference with no digits at all
   - Expected: _numeric("") equals `refused`
   - Expected: _numeric("x") equals `refused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a malformed number instead of decoding part of it")
step("offer a body with a non-digit in it")
expect(_numeric("12z4")).to_equal("refused")
step("offer a hexadecimal digit in a decimal reference")
expect(_numeric("1f")).to_equal("refused")
step("offer a reference with no digits at all")
expect(_numeric("")).to_equal("refused")
expect(_numeric("x")).to_equal("refused")
```

</details>

#### refuses a number that is not a character

- refuses a number that is not a character
- offer NUL, which HTML forbids
   - Expected: _numeric("0") equals `refused`
- offer a lone surrogate, which is not a scalar value
   - Expected: _numeric("xD800") equals `refused`
- offer a value above the last codepoint
   - Expected: _numeric("x110000") equals `refused`
   - Expected: _numeric("99999999") equals `refused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a number that is not a character")
step("offer NUL, which HTML forbids")
expect(_numeric("0")).to_equal("refused")
step("offer a lone surrogate, which is not a scalar value")
expect(_numeric("xD800")).to_equal("refused")
step("offer a value above the last codepoint")
expect(_numeric("x110000")).to_equal("refused")
expect(_numeric("99999999")).to_equal("refused")
```

</details>

#### leaves a refused numeric reference in the text exactly as written

- leaves a refused numeric reference in the text exactly as written
- decode a string containing an out-of-range reference
   - Expected: decode_character_references("a &#0; b") equals `a &#0; b`
- confirm the refusal was reported
   - Expected: _error_count("a &#0; b") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a refused numeric reference in the text exactly as written")
step("decode a string containing an out-of-range reference")
expect(decode_character_references("a &#0; b")).to_equal("a &#0; b")
step("confirm the refusal was reported")
expect(_error_count("a &#0; b")).to_equal(1)
```

</details>

### decoding an unterminated reference

#### leaves a reference with no semicolon untouched

- leaves a reference with no semicolon untouched
- decode text where the author omitted the closing semicolon
   - Expected: decode_character_references("a &amp b") equals `a &amp b`
   - Expected: decode_character_references("50 &#37 off") equals `50 &#37 off`
- confirm each omission was reported
   - Expected: _error_count("a &amp b") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a reference with no semicolon untouched")
step("decode text where the author omitted the closing semicolon")
expect(decode_character_references("a &amp b")).to_equal("a &amp b")
expect(decode_character_references("50 &#37 off")).to_equal("50 &#37 off")
step("confirm each omission was reported")
expect(_error_count("a &amp b")).to_equal(1)
```

</details>

#### stops at the next ampersand rather than swallowing the rest of a sentence

- stops at the next ampersand rather than swallowing the rest of a sentence
- decode prose with a bare ampersand followed by a real reference
   - Expected: decode_character_references("Tom & Jerry &amp; Co") equals `Tom & Jerry & Co`
- confirm exactly one refusal — the bare ampersand, not the good one
   - Expected: _error_count("Tom & Jerry &amp; Co") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at the next ampersand rather than swallowing the rest of a sentence")
step("decode prose with a bare ampersand followed by a real reference")
expect(decode_character_references("Tom & Jerry &amp; Co")).to_equal("Tom & Jerry & Co")
step("confirm exactly one refusal — the bare ampersand, not the good one")
expect(_error_count("Tom & Jerry &amp; Co")).to_equal(1)
```

</details>

#### leaves a lone trailing ampersand alone

- leaves a lone trailing ampersand alone
- decode a string ending in a bare ampersand
   - Expected: decode_character_references("a &") equals `a &`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a lone trailing ampersand alone")
step("decode a string ending in a bare ampersand")
expect(decode_character_references("a &")).to_equal("a &")
```

</details>

#### refuses an empty reference

- refuses an empty reference
- decode `&;`, which names nothing
   - Expected: decode_character_references("a &; b") equals `a &; b`
   - Expected: _error_count("a &; b") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an empty reference")
step("decode `&;`, which names nothing")
expect(decode_character_references("a &; b")).to_equal("a &; b")
expect(_error_count("a &; b")).to_equal(1)
```

</details>

### decoding a whole string

#### leaves text with no references byte-for-byte unchanged

- leaves text with no references byte-for-byte unchanged
- decode ordinary prose
   - Expected: decode_character_references("plain text, no refs") equals `plain text, no refs`
- confirm nothing was reported
   - Expected: _error_count("plain text, no refs") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves text with no references byte-for-byte unchanged")
step("decode ordinary prose")
expect(decode_character_references("plain text, no refs")).to_equal("plain text, no refs")
step("confirm nothing was reported")
expect(_error_count("plain text, no refs")).to_equal(0)
```

</details>

#### decodes several references in one pass

- decodes several references in one pass
- decode a string mixing named, decimal and hex forms
   - Expected: decode_character_references("&lt;b&gt;caf&#233;&#x2014;ok&lt;/b&gt;") equals `<b>café—ok</b>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes several references in one pass")
step("decode a string mixing named, decimal and hex forms")
expect(decode_character_references("&lt;b&gt;caf&#233;&#x2014;ok&lt;/b&gt;")).to_equal("<b>café—ok</b>")
```

</details>

#### decodes the good references and reports only the bad ones

- decodes the good references and reports only the bad ones
- decode a string with two good and two bad references
   - Expected: out.value equals `& &bogus; é &#0;`
- confirm both failures are named individually
   - Expected: out.errors.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes the good references and reports only the bad ones")
step("decode a string with two good and two bad references")
val out = decode_character_references_checked("&amp; &bogus; &#233; &#0;")
expect(out.value).to_equal("& &bogus; é &#0;")
step("confirm both failures are named individually")
expect(out.errors.len()).to_equal(2)
```

</details>

#### does not decode an already-decoded ampersand a second time

- does not decode an already-decoded ampersand a second time
- decode `&amp;amp;`, which must yield the literal text `&amp;`
   - Expected: decode_character_references("&amp;amp;") equals `&amp;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not decode an already-decoded ampersand a second time")
step("decode `&amp;amp;`, which must yield the literal text `&amp;`")
expect(decode_character_references("&amp;amp;")).to_equal("&amp;")
```

</details>

#### counts positions in codepoints, so a multi-byte character does not shift a reference

- counts positions in codepoints, so a multi-byte character does not shift a reference
- decode a reference that sits after non-ASCII text
   - Expected: decode_character_references("é&amp;é") equals `é&é`
   - Expected: decode_character_references("日本語 &#x2014; ok") equals `日本語 — ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts positions in codepoints, so a multi-byte character does not shift a reference")
step("decode a reference that sits after non-ASCII text")
expect(decode_character_references("é&amp;é")).to_equal("é&é")
expect(decode_character_references("日本語 &#x2014; ok")).to_equal("日本語 — ok")
```

</details>

### reading one reference out of a character array

#### reports how many characters a decoded reference consumed

- reports how many characters a decoded reference consumed
- match `&amp;` at the start of a character array
   - Expected: m.ok is true
   - Expected: m.value equals `&`
   - Expected: m.consumed equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports how many characters a decoded reference consumed")
step("match `&amp;` at the start of a character array")
val m = match_entity("&amp;x".chars(), 0)
expect(m.ok).to_equal(true)
expect(m.value).to_equal("&")
expect(m.consumed).to_equal(5)
```

</details>

#### consumes nothing and says why when it cannot decode

- consumes nothing and says why when it cannot decode
- match an unknown name
   - Expected: m.ok is false
   - Expected: m.consumed equals `0`
- confirm the reason names the reference, so a log is actionable
   - Expected: m.error contains `bogus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consumes nothing and says why when it cannot decode")
step("match an unknown name")
val m = match_entity("&bogus;".chars(), 0)
expect(m.ok).to_equal(false)
expect(m.consumed).to_equal(0)
step("confirm the reason names the reference, so a log is actionable")
expect(m.error.contains("bogus")).to_equal(true)
```

</details>

#### refuses a position that is not an ampersand at all

- refuses a position that is not an ampersand at all
- match at a position holding an ordinary letter
   - Expected: m.ok is false
   - Expected: m.consumed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a position that is not an ampersand at all")
step("match at a position holding an ordinary letter")
val m = match_entity("abc".chars(), 0)
expect(m.ok).to_equal(false)
expect(m.consumed).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-HTMLENT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `debb8aec55d02dddca7dc77625bf2154b6b8e162425b485ffb7819c4d688029c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `debb8aec55d02dddca7dc77625bf2154b6b8e162425b485ffb7819c4d688029c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `debb8aec55d02dddca7dc77625bf2154b6b8e162425b485ffb7819c4d688029c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/common/html/character_references_spec.spl
mirror: doc/06_spec/unit/lib/common/html/character_references_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/lib/common/html/character_references_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/lib/common/html/character_references_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/html/character_references_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/common/html/character_references_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the five references every document depends on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/html/character_references_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a name from the wider table, not just the core five' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/html/character_references_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads only the capitalisations HTML actually defines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
