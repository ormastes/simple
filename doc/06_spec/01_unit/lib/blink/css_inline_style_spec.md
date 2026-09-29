# Blink CSS Parser — Inline `style="..."` Attributes

> A page author writes `<div style="color: red; margin: 0">`. That attribute value

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink CSS Parser — Inline `style="..."` Attributes

A page author writes `<div style="color: red; margin: 0">`. That attribute value

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Implemented |
| Source | `test/01_unit/lib/blink/css_inline_style_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A page author writes `<div style="color: red; margin: 0">`. That attribute value
is a declaration list with no selector and no braces — nothing a stylesheet
parser that starts by looking for `{` can read. blink's parser previously took a
token stream only, with no raw-string entry point at all, so an inline style was
simply unreachable: the most common way styling reaches an element could not be
parsed. This spec covers the entry point that closes that gap.

## Scope and Preconditions

`parse_inline_style(source)` takes the raw attribute value exactly as HTML
delivers it and returns the declarations plus the list of things it refused.
`parse_declarations(source)` is the same call with the refusals discarded, for
callers that only want the good declarations.

Both share ONE declaration reader with `parse_css`, so a property that parses
inside a rule body parses identically inside a style attribute. That sharing is
the point: a second copy of the reader would drift, and inline styles would
start disagreeing with stylesheets about `!important` or about spacing inside
`calc()`.

## Primary Workflow

Each `property: value` pair becomes a declaration, with `!important` detected
the same way it is in a rule body. **A malformed declaration is dropped AND
reported** — a missing colon, a property name that is not an identifier, or an
empty value each append a message to `errors`. It is never stored with a
guessed or empty value, because an empty string reads to a consumer as a real
value and would silently blank the property.

Running out of tokens is the NORMAL end of an inline style — there is no `}` to
find — so it is not reported, while the same condition inside a rule body still
is.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `CssDeclarationBlock` | declarations + errors + the token position it stopped at. |
| Shared reader | `_parse_declaration_block` serves both entry points. |
| Reported refusal | A dropped declaration always leaves a message behind. |

## Compatibility and Limitations

An inline style holds declarations only. Selectors, at-rules and nesting are not
accepted here and are not silently tolerated.

## Related Specifications

- [Blink CSS parser](css_parser_spec.md) — the stylesheet entry point.

## Scenarios

### reading an inline style attribute

#### reads a single declaration written without a trailing semicolon

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a single declaration written without a trailing semicolon
- parse the shortest thing an author writes: `color: red`
   - Expected: _render("color: red") equals `color=red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a single declaration written without a trailing semicolon")
step("parse the shortest thing an author writes: `color: red`")
expect(_render("color: red")).to_equal("color=red")
```

</details>

#### reads several declarations separated by semicolons

- reads several declarations separated by semicolons
- parse a three-property attribute value
   - Expected: _render("color: red; margin: 0; display: block") equals `color=red|margin=0|display=block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads several declarations separated by semicolons")
step("parse a three-property attribute value")
expect(_render("color: red; margin: 0; display: block")).to_equal("color=red|margin=0|display=block")
```

</details>

#### reads a trailing semicolon as the end of the list, not a fourth declaration

- reads a trailing semicolon as the end of the list, not a fourth declaration
- parse a value the author terminated with `;`
   - Expected: _render("color: red; margin: 0;") equals `color=red|margin=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a trailing semicolon as the end of the list, not a fourth declaration")
step("parse a value the author terminated with `;`")
expect(_render("color: red; margin: 0;")).to_equal("color=red|margin=0")
```

</details>

#### reads a value that contains spaces as one value

- reads a value that contains spaces as one value
- parse a shorthand whose value has three space-separated parts
   - Expected: _render("border: 1px solid red") equals `border=1px solid red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a value that contains spaces as one value")
step("parse a shorthand whose value has three space-separated parts")
expect(_render("border: 1px solid red")).to_equal("border=1px solid red")
```

</details>

#### reads a value that contains a function call

- reads a value that contains a function call
- parse values holding rgb() and calc(), where spacing is significant
   - Expected: _render("color: rgb(1, 2, 3)") equals `color=rgb(1, 2, 3)`
   - Expected: _render("width: calc(100% - 2px)") equals `width=calc(100% - 2px)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a value that contains a function call")
step("parse values holding rgb() and calc(), where spacing is significant")
expect(_render("color: rgb(1, 2, 3)")).to_equal("color=rgb(1, 2, 3)")
expect(_render("width: calc(100% - 2px)")).to_equal("width=calc(100% - 2px)")
```

</details>

#### reads a hex colour with its leading sigil intact

- reads a hex colour with its leading sigil intact
- parse a hex colour, which the tokenizer strips the `#` from
   - Expected: _render("color: #1a2b3c") equals `color=#1a2b3c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a hex colour with its leading sigil intact")
step("parse a hex colour, which the tokenizer strips the `#` from")
expect(_render("color: #1a2b3c")).to_equal("color=#1a2b3c")
```

</details>

#### marks a declaration the author flagged as important

- marks a declaration the author flagged as important
- parse a value ending in `!important`
   - Expected: _render("color: red !important") equals `color=red!`
- parse a list where only the second declaration is flagged
   - Expected: _render("color: red; margin: 0 !important") equals `color=red|margin=0!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks a declaration the author flagged as important")
step("parse a value ending in `!important`")
expect(_render("color: red !important")).to_equal("color=red!")
step("parse a list where only the second declaration is flagged")
expect(_render("color: red; margin: 0 !important")).to_equal("color=red|margin=0!")
```

</details>

#### tolerates the whitespace an author actually types

- tolerates the whitespace an author actually types
- parse a value with no space after the colon and padding around it
   - Expected: _render("  color:red  ;  margin : 0  ") equals `color=red|margin=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tolerates the whitespace an author actually types")
step("parse a value with no space after the colon and padding around it")
expect(_render("  color:red  ;  margin : 0  ")).to_equal("color=red|margin=0")
```

</details>

#### reads an empty attribute value as no declarations and no complaints

- reads an empty attribute value as no declarations and no complaints
- parse an empty style attribute
   - Expected: _render("") equals ``
   - Expected: _error_count("") equals `0`
- parse an attribute holding only whitespace and semicolons
   - Expected: _render("  ;; ") equals ``
   - Expected: _error_count("  ;; ") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads an empty attribute value as no declarations and no complaints")
step("parse an empty style attribute")
expect(_render("")).to_equal("")
expect(_error_count("")).to_equal(0)
step("parse an attribute holding only whitespace and semicolons")
expect(_render("  ;; ")).to_equal("")
expect(_error_count("  ;; ")).to_equal(0)
```

</details>

### reading a malformed inline style attribute

#### drops a declaration with no colon and says so

- drops a declaration with no colon and says so
- parse an attribute where the author forgot the colon
   - Expected: _render("color red; margin: 0") equals `margin=0`
- confirm the drop was reported rather than passing unnoticed
   - Expected: _error_count("color red; margin: 0") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a declaration with no colon and says so")
step("parse an attribute where the author forgot the colon")
expect(_render("color red; margin: 0")).to_equal("margin=0")
step("confirm the drop was reported rather than passing unnoticed")
expect(_error_count("color red; margin: 0")).to_equal(1)
```

</details>

#### drops a property with an empty value rather than storing a blank

- drops a property with an empty value rather than storing a blank
- parse a declaration whose value the author left out
   - Expected: _render("color: ; margin: 0") equals `margin=0`
- confirm the drop was reported — a stored empty string would read as a real value
   - Expected: _error_count("color: ; margin: 0") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a property with an empty value rather than storing a blank")
step("parse a declaration whose value the author left out")
expect(_render("color: ; margin: 0")).to_equal("margin=0")
step("confirm the drop was reported — a stored empty string would read as a real value")
expect(_error_count("color: ; margin: 0")).to_equal(1)
```

</details>

#### drops a property name that is not an identifier and says so

- drops a property name that is not an identifier and says so
- parse an attribute starting with a number where a property belongs
   - Expected: _error_count("42: red") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a property name that is not an identifier and says so")
step("parse an attribute starting with a number where a property belongs")
expect(_error_count("42: red")).to_equal(1)
```

</details>

#### keeps every good declaration around a bad one

- keeps every good declaration around a bad one
- parse an attribute with a broken declaration between two sound ones
   - Expected: _render("color: red; oops; margin: 0") equals `color=red|margin=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps every good declaration around a bad one")
step("parse an attribute with a broken declaration between two sound ones")
expect(_render("color: red; oops; margin: 0")).to_equal("color=red|margin=0")
```

</details>

#### names the offending property in its message, so a log is actionable

- names the offending property in its message, so a log is actionable
- parse a declaration missing its colon and read the message
   - Expected: block.errors.len() equals `1`
   - Expected: block.errors.get(0) contains `color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names the offending property in its message, so a log is actionable")
step("parse a declaration missing its colon and read the message")
val block = parse_inline_style("color red")
expect(block.errors.len()).to_equal(1)
expect(block.errors.get(0).contains("color")).to_equal(true)
```

</details>

#### does not report running out of input, which is how an inline style ends

- does not report running out of input, which is how an inline style ends
- parse a well-formed attribute with no closing brace anywhere
   - Expected: _error_count("color: red; margin: 0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not report running out of input, which is how an inline style ends")
step("parse a well-formed attribute with no closing brace anywhere")
expect(_error_count("color: red; margin: 0")).to_equal(0)
```

</details>

### agreeing with the stylesheet parser

#### reads a declaration list identically whether or not it came from a rule body

- reads a declaration list identically whether or not it came from a rule body
- parse the same declarations through the inline entry point twice
- confirm the shared reader produced the same !important handling and spacing
   - Expected: a equals `color=red|border=1px solid blue!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a declaration list identically whether or not it came from a rule body")
step("parse the same declarations through the inline entry point twice")
val a = _render("color: red; border: 1px solid blue !important")
step("confirm the shared reader produced the same !important handling and spacing")
expect(a).to_equal("color=red|border=1px solid blue!")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINKINLINE-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9f1410c71bee854ae21e32d8dffaf01359093dfdf0dfea79367585d9eb2f4046`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f1410c71bee854ae21e32d8dffaf01359093dfdf0dfea79367585d9eb2f4046`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f1410c71bee854ae21e32d8dffaf01359093dfdf0dfea79367585d9eb2f4046`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/css_inline_style_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/css_inline_style_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/css_inline_style_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/css_inline_style_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/css_inline_style_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/css_inline_style_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/css_inline_style_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a single declaration written without a trailing semicolon' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/css_inline_style_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads several declarations separated by semicolons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/css_inline_style_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a trailing semicolon as the end of the list, not a fourth declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
