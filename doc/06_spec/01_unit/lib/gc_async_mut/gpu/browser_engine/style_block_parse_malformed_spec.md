# Style Block Parse Malformed Specification

> Tests covering style_block_parse @keyframes truncation, style_block_parse keyframe offsets and values, style_block_parse <style> extraction, style_block_parse at-rule flattening on truncated input, style_block_parse rule scanning on truncated input, style_block_parse nested-rule flattening, style_block_parse nested-rule tails, style_block_parse custom property resolution, style_block_parse background shorthand.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Block Parse Malformed Specification

## Scenarios

### style_block_parse @keyframes truncation

#### registers nothing when @keyframes has no opening brace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers nothing when @keyframes has no opening brace
   - Expected: kf_entry_count("@keyframes spin") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("registers nothing when @keyframes has no opening brace")
expect(kf_entry_count("@keyframes spin")).to_equal(0)
```

</details>

#### registers nothing when the @keyframes block is never closed

- registers nothing when the @keyframes block is never closed
   - Expected: kf_entry_count(css) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("registers nothing when the @keyframes block is never closed")
val css = "@keyframes spin " + lb() + "from" + lb() + "opacity:0" + rb()
expect(kf_entry_count(css)).to_equal(0)
```

</details>

#### registers an empty rule when a keyframe offset has no block

- registers an empty rule when a keyframe offset has no block
   - Expected: kf_frame_count(css) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("registers an empty rule when a keyframe offset has no block")
val css = "@keyframes spin " + lb() + " 0% opacity: 0 " + rb()
expect(kf_frame_count(css)).to_equal(0)
```

</details>

#### registers both keyframes of a well-formed rule

- registers both keyframes of a well-formed rule
   - Expected: kf_frame_count(css) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("registers both keyframes of a well-formed rule")
val css = ("@keyframes spin " + lb() + "from " + lb() + "opacity:0" + rb() +
           " to " + lb() + "opacity:1" + rb() + rb())
expect(kf_frame_count(css)).to_equal(2)
```

</details>

### style_block_parse keyframe offsets and values

#### accepts a percentage declaration value inside a keyframe

- accepts a percentage declaration value inside a keyframe
   - Expected: kf_frame_count(css) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a percentage declaration value inside a keyframe")
val css = "@keyframes g " + lb() + "from " + lb() + "width:50%" + rb() + rb()
expect(kf_frame_count(css)).to_equal(1)
```

</details>

#### rejects a percentage offset with no number at all

- rejects a percentage offset with no number at all
   - Expected: kf_frame_count(css) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a percentage offset with no number at all")
val css = "@keyframes g " + lb() + "% " + lb() + "opacity:0" + rb() + rb()
expect(kf_frame_count(css)).to_equal(0)
```

</details>

#### rejects a percentage offset that is only a sign

- rejects a percentage offset that is only a sign
   - Expected: kf_frame_count(css) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a percentage offset that is only a sign")
val css = "@keyframes g " + lb() + "+% " + lb() + "opacity:0" + rb() + rb()
expect(kf_frame_count(css)).to_equal(0)
```

</details>

#### rejects a percentage offset with two exponent markers

- rejects a percentage offset with two exponent markers
   - Expected: kf_frame_count(css) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a percentage offset with two exponent markers")
val css = "@keyframes g " + lb() + "1e2e3% " + lb() + "opacity:0" + rb() + rb()
expect(kf_frame_count(css)).to_equal(0)
```

</details>

#### accepts a signed exponent in a percentage offset

- accepts a signed exponent in a percentage offset
   - Expected: kf_frame_count(css) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a signed exponent in a percentage offset")
# 1e+1% is 10%, inside the 0..100 range.
val css = "@keyframes g " + lb() + "1e+1% " + lb() + "opacity:0" + rb() + rb()
expect(kf_frame_count(css)).to_equal(1)
```

</details>

#### rejects a non-digit in the exponent of a percentage offset

- rejects a non-digit in the exponent of a percentage offset
   - Expected: kf_frame_count(css) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-digit in the exponent of a percentage offset")
val css = "@keyframes g " + lb() + "1ex% " + lb() + "opacity:0" + rb() + rb()
expect(kf_frame_count(css)).to_equal(0)
```

</details>

### style_block_parse <style> extraction

#### finds no blocks in markup with no style tag

- finds no blocks in markup with no style tag
   - Expected: extract_style_blocks("<p>hi</p>").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds no blocks in markup with no style tag")
expect(extract_style_blocks("<p>hi</p>").len()).to_equal(0)
```

</details>

#### finds no blocks when the style tag is never closed with >

- finds no blocks when the style tag is never closed with >
   - Expected: extract_style_blocks("<p></p><style").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds no blocks when the style tag is never closed with >")
expect(extract_style_blocks("<p></p><style").len()).to_equal(0)
```

</details>

#### finds no blocks when </style> is missing

- finds no blocks when </style> is missing
   - Expected: extract_style_blocks("<style>p{color:red}").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds no blocks when </style> is missing")
expect(extract_style_blocks("<style>p{color:red}").len()).to_equal(0)
```

</details>

#### finds a well-formed style block

- finds a well-formed style block
   - Expected: extract_style_blocks(html).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds a well-formed style block")
val html = "<style>p " + lb() + "color:red" + rb() + "</style>"
expect(extract_style_blocks(html).len()).to_equal(1)
```

</details>

### style_block_parse at-rule flattening on truncated input

#### keeps the tail when @supports has no opening brace

- keeps the tail when @supports has no opening brace
   - Expected: parse_css_rules("@supports (display:flex)").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tail when @supports has no opening brace")
expect(parse_css_rules("@supports (display:flex)").len()).to_equal(0)
```

</details>

#### keeps the tail when the @supports block is never closed

- keeps the tail when the @supports block is never closed
   - Expected: parse_css_rules(css).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tail when the @supports block is never closed")
val css = "@supports (display:flex) " + lb() + "p " + lb() + "color:red" + rb()
expect(parse_css_rules(css).len()).to_equal(1)
```

</details>

#### keeps the tail when @layer has no opening brace

- keeps the tail when @layer has no opening brace
   - Expected: parse_css_rules("@layer base").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tail when @layer has no opening brace")
expect(parse_css_rules("@layer base").len()).to_equal(0)
```

</details>

#### keeps the tail when the @layer block is never closed

- keeps the tail when the @layer block is never closed
   - Expected: parse_css_rules(css).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tail when the @layer block is never closed")
val css = "@layer base " + lb() + "p " + lb() + "color:red" + rb()
expect(parse_css_rules(css).len()).to_equal(1)
```

</details>

#### keeps the tail when a trailing @keyframes has no opening brace

- keeps the tail when a trailing @keyframes has no opening brace
   - Expected: parse_css_rules(css).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tail when a trailing @keyframes has no opening brace")
val css = "p " + lb() + "color:red" + rb() + " @keyframes spin"
expect(parse_css_rules(css).len()).to_equal(1)
```

</details>

#### keeps the tail when a trailing @keyframes block is never closed

- keeps the tail when a trailing @keyframes block is never closed
   - Expected: parse_css_rules(css).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the tail when a trailing @keyframes block is never closed")
val css = ("p " + lb() + "color:red" + rb() + " @keyframes spin " + lb() +
           "from " + lb() + "opacity:0" + rb())
expect(parse_css_rules(css).len()).to_equal(2)
```

</details>

### style_block_parse rule scanning on truncated input

#### parses no rule when there is no opening brace at all

- parses no rule when there is no opening brace at all
   - Expected: parse_css_rules("p color: red").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses no rule when there is no opening brace at all")
expect(parse_css_rules("p color: red").len()).to_equal(0)
```

</details>

#### skips a block whose selector is empty and keeps the next rule

- skips a block whose selector is empty and keeps the next rule
   - Expected: parse_css_rules(css).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips a block whose selector is empty and keeps the next rule")
val css = lb() + "color:red" + rb() + " p " + lb() + "color:blue" + rb()
expect(parse_css_rules(css).len()).to_equal(1)
```

</details>

#### parses no rule when the closing brace is missing

- parses no rule when the closing brace is missing
   - Expected: parse_css_rules("p " + lb() + "color:red").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses no rule when the closing brace is missing")
expect(parse_css_rules("p " + lb() + "color:red").len()).to_equal(0)
```

</details>

### style_block_parse nested-rule flattening

#### keeps trailing declarations after the last nested block

- keeps trailing declarations after the last nested block
   - Expected: parse_css_rules(css).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps trailing declarations after the last nested block")
val css = ("p " + lb() + "color:red; & span " + lb() + "color:blue" + rb() +
           " trailing" + rb())
expect(parse_css_rules(css).len()).to_equal(2)
```

</details>

#### drops a nested at-rule that cannot be combined with its parent

- drops a nested at-rule that cannot be combined with its parent
   - Expected: parse_css_rules(css).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a nested at-rule that cannot be combined with its parent")
val css = "p " + lb() + "@media screen " + lb() + "color:blue" + rb() + rb()
expect(parse_css_rules(css).len()).to_equal(1)
```

</details>

#### parses two sibling rules unchanged

- parses two sibling rules unchanged
   - Expected: parse_css_rules(css).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses two sibling rules unchanged")
val css = "p " + lb() + "color:red" + rb() + " a " + lb() + "color:blue" + rb()
expect(parse_css_rules(css).len()).to_equal(2)
```

</details>

### style_block_parse nested-rule tails

#### keeps declarations that follow the last nested block

- keeps declarations that follow the last nested block
   - Expected: parse_css_rules(css).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps declarations that follow the last nested block")
val css = "p " + lb() + "& span " + lb() + "color:blue" + rb() + " color:red" + rb()
expect(parse_css_rules(css).len()).to_equal(2)
```

</details>

#### drops a nested at-rule while keeping a sibling parent-reference rule

- drops a nested at-rule while keeping a sibling parent-reference rule
   - Expected: parse_css_rules(css).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a nested at-rule while keeping a sibling parent-reference rule")
val css = ("p " + lb() + "@media screen " + lb() + "color:blue" + rb() +
           " & a " + lb() + "color:red" + rb() + rb())
expect(parse_css_rules(css).len()).to_equal(1)
```

</details>

### style_block_parse custom property resolution

#### substitutes a defined custom property

- substitutes a defined custom property
   - Expected: resolved_value(css, "color") equals `teal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("substitutes a defined custom property")
val css = ":root " + lb() + "--brand: teal" + rb() + " p " + lb() + "color: var(--brand)" + rb()
expect(resolved_value(css, "color")).to_equal("teal")
```

</details>

#### falls back when the custom property is undefined

- falls back when the custom property is undefined
   - Expected: resolved_value(css, "color") equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back when the custom property is undefined")
val css = (":root " + lb() + "--brand: teal" + rb() + " p " + lb() +
           "color: var(--missing, blue)" + rb())
expect(resolved_value(css, "color")).to_equal("blue")
```

</details>

#### leaves the reference intact when undefined with no fallback

- leaves the reference intact when undefined with no fallback
   - Expected: resolved_value(css, "color") equals `var(--missing)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves the reference intact when undefined with no fallback")
val css = (":root " + lb() + "--brand: teal" + rb() + " p " + lb() +
           "color: var(--missing)" + rb())
expect(resolved_value(css, "color")).to_equal("var(--missing)")
```

</details>

#### leaves an empty var() reference intact

- leaves an empty var() reference intact
   - Expected: resolved_value(css, "color") equals `var()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves an empty var() reference intact")
val css = ":root " + lb() + "--brand: teal" + rb() + " p " + lb() + "color: var()" + rb()
expect(resolved_value(css, "color")).to_equal("var()")
```

</details>

#### leaves an unterminated var( reference intact

- leaves an unterminated var( reference intact
   - Expected: resolved_value(css, "color") equals `var(--brand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves an unterminated var( reference intact")
val css = ":root " + lb() + "--brand: teal" + rb() + " p " + lb() + "color: var(--brand" + rb()
expect(resolved_value(css, "color")).to_equal("var(--brand")
```

</details>

#### returns the rules untouched when no custom properties were collected

- returns the rules untouched when no custom properties were collected
   - Expected: resolved_value(css, "color") equals `var(--brand)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the rules untouched when no custom properties were collected")
val css = "p " + lb() + "color: var(--brand)" + rb()
expect(resolved_value(css, "color")).to_equal("var(--brand)")
```

</details>

### style_block_parse background shorthand

#### keeps a bare color as background-color

- keeps a bare color as background-color
   - Expected: decl_props("background: red") equals `background-color=red;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a bare color as background-color")
expect(decl_props("background: red")).to_equal("background-color=red;")
```

</details>

#### keeps a gradient as background

- keeps a gradient as background


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a gradient as background")
expect(decl_props("background: linear-gradient(red, blue)")).to_equal(
    "background=linear-gradient(red, blue);")
```

</details>

#### keeps two url() layers as background

- keeps two url() layers as background


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps two url() layers as background")
expect(decl_props("background: url(a.png) url(b.png)")).to_equal(
    "background=url(a.png) url(b.png);")
```

</details>

#### keeps an unterminated url( as background

- keeps an unterminated url( as background
   - Expected: decl_props("background: url(") equals `background=url(;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an unterminated url( as background")
expect(decl_props("background: url(")).to_equal("background=url(;")
```

</details>

#### emits nothing for a declaration with an empty value

- emits nothing for a declaration with an empty value
   - Expected: decl_props("background:") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits nothing for a declaration with an empty value")
expect(decl_props("background:")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering style_block_parse @keyframes truncation, style_block_parse keyframe offsets and values, style_block_parse <style> extraction, style_block_parse at-rule flattening on truncated input, style_block_parse rule scanning on truncated input, style_block_parse nested-rule flattening, style_block_parse nested-rule tails, style_block_parse custom property resolution, style_block_parse background shorthand.
- style_block_parse @keyframes truncation
- style_block_parse keyframe offsets and values
- style_block_parse <style> extraction
- style_block_parse at-rule flattening on truncated input
- style_block_parse rule scanning on truncated input
- style_block_parse nested-rule flattening
- style_block_parse nested-rule tails
- style_block_parse custom property resolution
- style_block_parse background shorthand

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
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

- Canonical SPipe generation for source `4597abd316149133c647778c2030ff3b34122fec70473d9a7f4f8f85cc8b3259`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4597abd316149133c647778c2030ff3b34122fec70473d9a7f4f8f85cc8b3259`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4597abd316149133c647778c2030ff3b34122fec70473d9a7f4f8f85cc8b3259`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers nothing when @keyframes has no opening brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers nothing when the @keyframes block is never closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_parse_malformed_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers an empty rule when a keyframe offset has no block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
