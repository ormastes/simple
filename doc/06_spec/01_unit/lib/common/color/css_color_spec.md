# Shared CSS Colour Parsing

> A CSS author writes a colour in whatever notation the property allows —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared CSS Colour Parsing

A CSS author writes a colour in whatever notation the property allows —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/color/css_color_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A CSS author writes a colour in whatever notation the property allows —
`rebeccapurple`, `#1a2b3c`, `rgba(255, 128, 0, 0.5)`, `hsl(240deg 100% 50% /
25%)` — and expects every renderer in this repo to read it the same way. This
module is the single place that reading happens, so a lane that renders CSS
imports it instead of growing its own table.

## Scope and Preconditions

`parse_css_color` accepts one CSS colour token. The CSS Level 4 named table
(148 names, including the `grey`, `aqua` and `fuchsia` aliases and
`transparent`), `#RGB`/`#RGBA`/`#RRGGBB`/`#RRGGBBAA`, and `rgb()`/`rgba()`/
`hsl()`/`hsla()` in both the legacy comma form and the modern space-plus-slash
form, with percentage channels.

## Primary Workflow

A supported colour comes back as a `Color` with 0..255 channels. **An
unsupported colour comes back as `nil`** — the reason this spec exists. Before
this module the callers answered opaque black for anything they did not
recognise, which paints a wrong pixel that no smoke test can see, and is
exactly why the gap between a nine-colour table and real CSS went unnoticed.
Every unsupported form below is covered on purpose.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `nil` result | The colour is unsupported. Never a substituted colour. |
| Legacy form | `rgb(a, b, c)` — comma separated, optional fourth alpha. |
| Modern form | `rgb(a b c / alpha)` — space separated, slash before alpha. |

## Related Specifications

- [Style Cascade](../../blink/style_cascade_spec.md) — blink's consumer.

## Scenarios

### reading a CSS colour by name

#### reads a name from the full CSS Level 4 table, not a nine-colour subset

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a name from the full CSS Level 4 table, not a nine-colour subset
- read `rebeccapurple`, a name outside any short built-in list
   - Expected: _read("rebeccapurple") equals `102,51,153,255`
- read `cornflowerblue` and `mediumspringgreen` from the same table
   - Expected: _read("cornflowerblue") equals `100,149,237,255`
   - Expected: _read("mediumspringgreen") equals `0,250,154,255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a name from the full CSS Level 4 table, not a nine-colour subset")
step("read `rebeccapurple`, a name outside any short built-in list")
expect(_read("rebeccapurple")).to_equal("102,51,153,255")
step("read `cornflowerblue` and `mediumspringgreen` from the same table")
expect(_read("cornflowerblue")).to_equal("100,149,237,255")
expect(_read("mediumspringgreen")).to_equal("0,250,154,255")
```

</details>

#### reads a name case-insensitively

- reads a name case-insensitively
- read `Grey` with a capital, as an author may have typed it
   - Expected: _read("Grey") equals `128,128,128,255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a name case-insensitively")
step("read `Grey` with a capital, as an author may have typed it")
expect(_read("Grey")).to_equal("128,128,128,255")
```

</details>

#### reads the spelling aliases as the same colour

- reads the spelling aliases as the same colour
- read the `gray`/`grey` and `cyan`/`aqua` alias pairs
   - Expected: _read("gray") equals `_read("grey")`
   - Expected: _read("cyan") equals `_read("aqua")`
   - Expected: _read("magenta") equals `_read("fuchsia")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the spelling aliases as the same colour")
step("read the `gray`/`grey` and `cyan`/`aqua` alias pairs")
expect(_read("gray")).to_equal(_read("grey"))
expect(_read("cyan")).to_equal(_read("aqua"))
expect(_read("magenta")).to_equal(_read("fuchsia"))
```

</details>

#### reads `transparent` as fully transparent, not as black

- reads `transparent` as fully transparent, not as black
- read `transparent`
   - Expected: _read("transparent") equals `0,0,0,0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads `transparent` as fully transparent, not as black")
step("read `transparent`")
expect(_read("transparent")).to_equal("0,0,0,0")
```

</details>

#### reports an unknown name as unsupported instead of guessing a colour

- reports an unknown name as unsupported instead of guessing a colour
- read `notacolour`, which is not in the CSS table
   - Expected: _read("notacolour") equals `nil`
- read `burntsienna`, a plausible but non-CSS name
   - Expected: _read("burntsienna") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an unknown name as unsupported instead of guessing a colour")
step("read `notacolour`, which is not in the CSS table")
expect(_read("notacolour")).to_equal("nil")
step("read `burntsienna`, a plausible but non-CSS name")
expect(_read("burntsienna")).to_equal("nil")
```

</details>

### reading a CSS colour in hex notation

#### reads all four hex lengths

- reads all four hex lengths
- read #RGB, #RGBA, #RRGGBB and #RRGGBBAA
   - Expected: _read("#f00") equals `255,0,0,255`
   - Expected: _read("#f008") equals `255,0,0,136`
   - Expected: _read("#FF8000") equals `255,128,0,255`
   - Expected: _read("#11223344") equals `17,34,51,68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads all four hex lengths")
step("read #RGB, #RGBA, #RRGGBB and #RRGGBBAA")
expect(_read("#f00")).to_equal("255,0,0,255")
expect(_read("#f008")).to_equal("255,0,0,136")
expect(_read("#FF8000")).to_equal("255,128,0,255")
expect(_read("#11223344")).to_equal("17,34,51,68")
```

</details>

#### reports a non-hex digit as unsupported instead of reading it as zero

- reports a non-hex digit as unsupported instead of reading it as zero
- read `#gg0000`, where the red channel is not hex at all
   - Expected: _read("#gg0000") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a non-hex digit as unsupported instead of reading it as zero")
step("read `#gg0000`, where the red channel is not hex at all")
expect(_read("#gg0000")).to_equal("nil")
```

</details>

#### reports a hex string of the wrong length as unsupported

- reports a hex string of the wrong length as unsupported
- read `#ff00`-style lengths CSS does not define
   - Expected: _read("#ff") equals `nil`
   - Expected: _read("#fffff") equals `nil`
   - Expected: _read("#1234567") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a hex string of the wrong length as unsupported")
step("read `#ff00`-style lengths CSS does not define")
expect(_read("#ff")).to_equal("nil")
expect(_read("#fffff")).to_equal("nil")
expect(_read("#1234567")).to_equal("nil")
```

</details>

### reading a CSS colour in rgb() notation

#### reads the legacy comma form with and without alpha

- reads the legacy comma form with and without alpha
- read `rgb(255, 128, 0)` and `rgba(255, 128, 0, 0.5)`
   - Expected: _read("rgb(255, 128, 0)") equals `255,128,0,255`
   - Expected: _read("rgba(255, 128, 0, 0.5)") equals `255,128,0,128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the legacy comma form with and without alpha")
step("read `rgb(255, 128, 0)` and `rgba(255, 128, 0, 0.5)`")
expect(_read("rgb(255, 128, 0)")).to_equal("255,128,0,255")
expect(_read("rgba(255, 128, 0, 0.5)")).to_equal("255,128,0,128")
```

</details>

#### reads the modern space form with a slash alpha

- reads the modern space form with a slash alpha
- read `rgb(255 128 0 / 50%)`
   - Expected: _read("rgb(255 128 0 / 50%)") equals `255,128,0,128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the modern space form with a slash alpha")
step("read `rgb(255 128 0 / 50%)`")
expect(_read("rgb(255 128 0 / 50%)")).to_equal("255,128,0,128")
```

</details>

#### reads percentage channels

- reads percentage channels
- read `rgb(100%, 50%, 0%)`
   - Expected: _read("rgb(100%, 50%, 0%)") equals `255,128,0,255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads percentage channels")
step("read `rgb(100%, 50%, 0%)`")
expect(_read("rgb(100%, 50%, 0%)")).to_equal("255,128,0,255")
```

</details>

#### clamps a channel outside 0..255 rather than wrapping it

- clamps a channel outside 0..255 rather than wrapping it
- read `rgb(300, -20, 0)`
   - Expected: _read("rgb(300, -20, 0)") equals `255,0,0,255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps a channel outside 0..255 rather than wrapping it")
step("read `rgb(300, -20, 0)`")
expect(_read("rgb(300, -20, 0)")).to_equal("255,0,0,255")
```

</details>

#### reports a non-numeric channel as unsupported instead of reading it as zero

- reports a non-numeric channel as unsupported instead of reading it as zero
- read `rgb(red, 0, 0)`, whose first channel is a name
   - Expected: _read("rgb(red, 0, 0)") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a non-numeric channel as unsupported instead of reading it as zero")
step("read `rgb(red, 0, 0)`, whose first channel is a name")
expect(_read("rgb(red, 0, 0)")).to_equal("nil")
```

</details>

#### reports a wrong argument count as unsupported

- reports a wrong argument count as unsupported
- read `rgb(1, 2)` and `rgb(1, 2, 3, 4, 5)`
   - Expected: _read("rgb(1, 2)") equals `nil`
   - Expected: _read("rgb(1, 2, 3, 4, 5)") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a wrong argument count as unsupported")
step("read `rgb(1, 2)` and `rgb(1, 2, 3, 4, 5)`")
expect(_read("rgb(1, 2)")).to_equal("nil")
expect(_read("rgb(1, 2, 3, 4, 5)")).to_equal("nil")
```

</details>

#### reports a mixed comma-and-slash argument list as unsupported

- reports a mixed comma-and-slash argument list as unsupported
- read `rgb(1, 2, 3 / 0.5)`, which is neither CSS form
   - Expected: _read("rgb(1, 2, 3 / 0.5)") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a mixed comma-and-slash argument list as unsupported")
step("read `rgb(1, 2, 3 / 0.5)`, which is neither CSS form")
expect(_read("rgb(1, 2, 3 / 0.5)")).to_equal("nil")
```

</details>

#### reports an unclosed function as unsupported

- reports an unclosed function as unsupported
- read `rgb(255, 0, 0` with no closing parenthesis
   - Expected: _read("rgb(255, 0, 0") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an unclosed function as unsupported")
step("read `rgb(255, 0, 0` with no closing parenthesis")
expect(_read("rgb(255, 0, 0")).to_equal("nil")
```

</details>

### reading a CSS colour in hsl() notation

#### reads the legacy comma form with and without alpha

- reads the legacy comma form with and without alpha
- read `hsl(120, 100%, 50%)` and `hsla(0, 100%, 50%, 0.5)`
   - Expected: _read("hsl(120, 100%, 50%)") equals `0,255,0,255`
   - Expected: _read("hsla(0, 100%, 50%, 0.5)") equals `255,0,0,128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the legacy comma form with and without alpha")
step("read `hsl(120, 100%, 50%)` and `hsla(0, 100%, 50%, 0.5)`")
expect(_read("hsl(120, 100%, 50%)")).to_equal("0,255,0,255")
expect(_read("hsla(0, 100%, 50%, 0.5)")).to_equal("255,0,0,128")
```

</details>

#### reads the modern space form with a deg hue and a slash alpha

- reads the modern space form with a deg hue and a slash alpha
- read `hsl(240deg 100% 50% / 25%)`
   - Expected: _read("hsl(240deg 100% 50% / 25%)") equals `0,0,255,64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads the modern space form with a deg hue and a slash alpha")
step("read `hsl(240deg 100% 50% / 25%)`")
expect(_read("hsl(240deg 100% 50% / 25%)")).to_equal("0,0,255,64")
```

</details>

#### normalises a hue outside 0..360 rather than rejecting it

- normalises a hue outside 0..360 rather than rejecting it
- read `hsl(480, 100%, 50%)`, which is 120 degrees round the wheel
   - Expected: _read("hsl(480, 100%, 50%)") equals `_read("hsl(120, 100%, 50%)")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalises a hue outside 0..360 rather than rejecting it")
step("read `hsl(480, 100%, 50%)`, which is 120 degrees round the wheel")
expect(_read("hsl(480, 100%, 50%)")).to_equal(_read("hsl(120, 100%, 50%)"))
```

</details>

#### reports a saturation or lightness without a percent sign as unsupported

- reports a saturation or lightness without a percent sign as unsupported
- read `hsl(120, 100, 50)`, which CSS does not allow unitless
   - Expected: _read("hsl(120, 100, 50)") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a saturation or lightness without a percent sign as unsupported")
step("read `hsl(120, 100, 50)`, which CSS does not allow unitless")
expect(_read("hsl(120, 100, 50)")).to_equal("nil")
```

</details>

### reading a colour syntax this module does not support

#### reports every unsupported colour function as unsupported, never as black

- reports every unsupported colour function as unsupported, never as black
- read the colour functions outside this module's scope
   - Expected: _read("color-mix(in srgb, red, blue)") equals `nil`
   - Expected: _read("lab(50% 40 59.5)") equals `nil`
   - Expected: _read("oklch(0.7 0.1 200)") equals `nil`
   - Expected: _read("hwb(120 30% 20%)") equals `nil`
   - Expected: _read("color(display-p3 1 0 0)") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports every unsupported colour function as unsupported, never as black")
step("read the colour functions outside this module's scope")
expect(_read("color-mix(in srgb, red, blue)")).to_equal("nil")
expect(_read("lab(50% 40 59.5)")).to_equal("nil")
expect(_read("oklch(0.7 0.1 200)")).to_equal("nil")
expect(_read("hwb(120 30% 20%)")).to_equal("nil")
expect(_read("color(display-p3 1 0 0)")).to_equal("nil")
```

</details>

#### reports the context-dependent keywords as unsupported

- reports the context-dependent keywords as unsupported
- read `currentColor` and `var(--brand)`, which need context this module has none of
   - Expected: _read("currentColor") equals `nil`
   - Expected: _read("var(--brand)") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the context-dependent keywords as unsupported")
step("read `currentColor` and `var(--brand)`, which need context this module has none of")
expect(_read("currentColor")).to_equal("nil")
expect(_read("var(--brand)")).to_equal("nil")
```

</details>

#### reports an empty value as unsupported

- reports an empty value as unsupported
- read an empty and a whitespace-only value
   - Expected: _read("") equals `nil`
   - Expected: _read("   ") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an empty value as unsupported")
step("read an empty and a whitespace-only value")
expect(_read("")).to_equal("nil")
expect(_read("   ")).to_equal("nil")
```

</details>

### the narrower entry points

#### named_color answers only names

- named_color answers only names
- ask named_color for a name and then for a hex string
   - Expected: c.r equals `255`
   - Expected: c.g equals `99`
   - Expected: c.b equals `71`
   - Expected: "tomato resolved" equals `tomato did not resolve`
   - Expected: named_color("#ff0000") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("named_color answers only names")
step("ask named_color for a name and then for a hex string")
if val c = named_color("tomato"):
    expect(c.r).to_equal(255)
    expect(c.g).to_equal(99)
    expect(c.b).to_equal(71)
else:
    expect("tomato resolved").to_equal("tomato did not resolve")
expect(named_color("#ff0000") == nil).to_equal(true)
```

</details>

#### parse_hex_color answers only hex strings

- parse_hex_color answers only hex strings
- ask parse_hex_color for a hex string and then for a name
   - Expected: c.g equals `255`
   - Expected: "#00ff00 resolved" equals `#00ff00 did not resolve`
   - Expected: parse_hex_color("red") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parse_hex_color answers only hex strings")
step("ask parse_hex_color for a hex string and then for a name")
if val c = parse_hex_color("#00ff00"):
    expect(c.g).to_equal(255)
else:
    expect("#00ff00 resolved").to_equal("#00ff00 did not resolve")
expect(parse_hex_color("red") == nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-CSSCOLOR-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0682623c532018c50bf829acc8b700e62abbb0a7e27ab6671b234bc23492b0b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0682623c532018c50bf829acc8b700e62abbb0a7e27ab6671b234bc23492b0b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0682623c532018c50bf829acc8b700e62abbb0a7e27ab6671b234bc23492b0b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/color/css_color_spec.spl
mirror: doc/06_spec/01_unit/lib/common/color/css_color_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/color/css_color_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/color/css_color_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/color/css_color_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/color/css_color_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/color/css_color_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a name from the full CSS Level 4 table, not a nine-colour subset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/css_color_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a name case-insensitively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/css_color_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the spelling aliases as the same colour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
