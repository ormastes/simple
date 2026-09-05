# CSS Length and `calc()` Resolution Specification

> `common.css.length` turns CSS length syntax — a plain dimension, a percentage, or a `calc()` expression — into a number of CSS pixels, or into an explained failure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Length and `calc()` Resolution Specification

`common.css.length` turns CSS length syntax — a plain dimension, a percentage, or a `calc()` expression — into a number of CSS pixels, or into an explained failure.

## At a Glance

| Field | Value |
|-------|-------|
| Category | CSS / Values |
| Status | Active |
| Source | `test/01_unit/lib/common/css/length_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`common.css.length` turns CSS length syntax — a plain dimension, a percentage,
or a `calc()` expression — into a number of CSS pixels, or into an explained
failure.

The failure half is the point of this specification. The sibling colour reader
used to answer opaque black for every notation it did not understand, and the
gap survived for months because a wrong colour still looks like a colour. A
length behaves the same way: a silent `0` still lays out. So every form this
module rejects is asserted here to report `ok = false`, and no rejected form is
allowed to come back as a number.

The resolution context used throughout is deliberately asymmetric so that a
mistake cannot hide behind equal values:

  - font size 16px, root font size 10px — so `em` and `rem` differ,
  - viewport 800 x 600 CSS px — so `vw`, `vh`, `vmin` and `vmax` all differ,
  - percentage basis 200px — so a percentage differs from all of the above.

## Scenarios

### plain CSS dimensions

#### resolves absolute units by their fixed ratio to the CSS pixel

- resolves absolute units by their fixed ratio to the CSS pixel
- 1in is 96px by definition — the CSS pixel is defined as 1/96in
   - Expected: _read("1in") equals `96.0`
- 1pt is 1/72in, so 96/72 = 1.333px
   - Expected: _read("1pt") equals `1.333`
- 1pc is 12pt, so 12 * 96/72 = 16px
   - Expected: _read("1pc") equals `16.0`
- 1cm is 96/2.54 = 37.795px
   - Expected: _read("1cm") equals `37.795`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves absolute units by their fixed ratio to the CSS pixel")
step("1in is 96px by definition — the CSS pixel is defined as 1/96in")
expect(_read("1in")).to_equal("96.0")
step("1pt is 1/72in, so 96/72 = 1.333px")
expect(_read("1pt")).to_equal("1.333")
step("1pc is 12pt, so 12 * 96/72 = 16px")
expect(_read("1pc")).to_equal("16.0")
step("1cm is 96/2.54 = 37.795px")
expect(_read("1cm")).to_equal("37.795")
```

</details>

#### resolves em against the element font and rem against the root font

- resolves em against the element font and rem against the root font
- font size is 16px, so 2em is 32px
   - Expected: _read("2em") equals `32.0`
- root font size is 10px, so 2rem is 20px — different on purpose
   - Expected: _read("2rem") equals `20.0`
- ex and ch use the CSS fallback of 0.5em, so 1ex of 16px is 8px
   - Expected: _read("1ex") equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves em against the element font and rem against the root font")
step("font size is 16px, so 2em is 32px")
expect(_read("2em")).to_equal("32.0")
step("root font size is 10px, so 2rem is 20px — different on purpose")
expect(_read("2rem")).to_equal("20.0")
step("ex and ch use the CSS fallback of 0.5em, so 1ex of 16px is 8px")
expect(_read("1ex")).to_equal("8.0")
```

</details>

#### resolves viewport units against the 800x600 viewport

- resolves viewport units against the 800x600 viewport
- 1vw is 1% of the 800px width = 8px
   - Expected: _read("1vw") equals `8.0`
- 1vh is 1% of the 600px height = 6px
   - Expected: _read("1vh") equals `6.0`
- vmin takes the smaller axis, the 600px height, so 1vmin is 6px
   - Expected: _read("1vmin") equals `6.0`
- vmax takes the larger axis, the 800px width, so 1vmax is 8px
   - Expected: _read("1vmax") equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves viewport units against the 800x600 viewport")
step("1vw is 1% of the 800px width = 8px")
expect(_read("1vw")).to_equal("8.0")
step("1vh is 1% of the 600px height = 6px")
expect(_read("1vh")).to_equal("6.0")
step("vmin takes the smaller axis, the 600px height, so 1vmin is 6px")
expect(_read("1vmin")).to_equal("6.0")
step("vmax takes the larger axis, the 800px width, so 1vmax is 8px")
expect(_read("1vmax")).to_equal("8.0")
```

</details>

#### accepts a signed magnitude and the bare unitless zero

- accepts a signed magnitude and the bare unitless zero
- a negative margin is legal CSS: -1.5em of a 16px font is -24px
   - Expected: _read("-1.5em") equals `-24.0`
- an explicit plus sign is the same value as no sign
   - Expected: _read("+12px") equals `12.0`
- 0 is the one unitless value CSS accepts as a length
   - Expected: _read("0") equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a signed magnitude and the bare unitless zero")
step("a negative margin is legal CSS: -1.5em of a 16px font is -24px")
expect(_read("-1.5em")).to_equal("-24.0")
step("an explicit plus sign is the same value as no sign")
expect(_read("+12px")).to_equal("12.0")
step("0 is the one unitless value CSS accepts as a length")
expect(_read("0")).to_equal("0.0")
```

</details>

### percentage resolution

#### resolves a percentage against the caller-supplied basis

- resolves a percentage against the caller-supplied basis
- the basis is 200px, so 50% is 100px
   - Expected: _read("50%") equals `100.0`
- percentages above 100 are legal: 150% of 200px is 300px
   - Expected: _read("150%") equals `300.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves a percentage against the caller-supplied basis")
step("the basis is 200px, so 50% is 100px")
expect(_read("50%")).to_equal("100.0")
step("percentages above 100 are legal: 150% of 200px is 300px")
expect(_read("150%")).to_equal("300.0")
```

</details>

#### fails a percentage when the context declares no basis

- fails a percentage when the context declares no basis
- length_context_no_percent has no basis; 50% must not become 0px
   - Expected: r.ok is false
- an absolute unit still resolves in that same context
   - Expected: abs.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails a percentage when the context declares no basis")
step("length_context_no_percent has no basis; 50% must not become 0px")
val r = parse_length_px("50%", length_context_no_percent(16.0, 10.0))
expect(r.ok).to_equal(false)
step("an absolute unit still resolves in that same context")
val abs = parse_length_px("4px", length_context_no_percent(16.0, 10.0))
expect(abs.ok).to_equal(true)
```

</details>

### calc() arithmetic

#### subtracts a fixed length from a percentage

- subtracts a fixed length from a percentage
- 50% of the 200px basis is 100px; minus 20px leaves 80px
   - Expected: _read("calc(50% - 20px)") equals `80.0`
- mixing em with px works the same way: 2em is 32px, plus 8px is 40px
   - Expected: _read("calc(2em + 8px)") equals `40.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("subtracts a fixed length from a percentage")
step("50% of the 200px basis is 100px; minus 20px leaves 80px")
expect(_read("calc(50% - 20px)")).to_equal("80.0")
step("mixing em with px works the same way: 2em is 32px, plus 8px is 40px")
expect(_read("calc(2em + 8px)")).to_equal("40.0")
```

</details>

#### gives multiplication and division higher precedence than addition

- gives multiplication and division higher precedence than addition
- 10px + 2 * 5px is 10 + 10 = 20px, not (10 + 2) * 5 = 60px
   - Expected: _read("calc(10px + 2 * 5px)") equals `20.0`
- 100px - 30px / 3 is 100 - 10 = 90px, not (100 - 30) / 3 = 23.3px
   - Expected: _read("calc(100px - 30px / 3)") equals `90.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives multiplication and division higher precedence than addition")
step("10px + 2 * 5px is 10 + 10 = 20px, not (10 + 2) * 5 = 60px")
expect(_read("calc(10px + 2 * 5px)")).to_equal("20.0")
step("100px - 30px / 3 is 100 - 10 = 90px, not (100 - 30) / 3 = 23.3px")
expect(_read("calc(100px - 30px / 3)")).to_equal("90.0")
```

</details>

#### lets parentheses override precedence and nest to any depth

- lets parentheses override precedence and nest to any depth
- parenthesising the sum makes (10 + 2) * 5 = 60px
   - Expected: _read("calc((10px + 2px) * 5)") equals `60.0`
- nested parentheses: ((4px + 1px) * 2) + 1px is 11px
   - Expected: _read("calc(((4px + 1px) * 2) + 1px)") equals `11.0`
- a nested calc() is legal and behaves as a parenthesised group
   - Expected: _read("calc(10px + calc(5px * 2))") equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets parentheses override precedence and nest to any depth")
step("parenthesising the sum makes (10 + 2) * 5 = 60px")
expect(_read("calc((10px + 2px) * 5)")).to_equal("60.0")
step("nested parentheses: ((4px + 1px) * 2) + 1px is 11px")
expect(_read("calc(((4px + 1px) * 2) + 1px)")).to_equal("11.0")
step("a nested calc() is legal and behaves as a parenthesised group")
expect(_read("calc(10px + calc(5px * 2))")).to_equal("20.0")
```

</details>

#### keeps fractional precision through division and percentages

- keeps fractional precision through division and percentages
- 100% of 200px divided by 3 is 66.667px — an integer division would truncate this to 66 and shift a layout by two thirds of a pixel
   - Expected: _read("calc(100% / 3)") equals `66.667`
- 10px / 4 is 2.5px, not 2px
   - Expected: _read("calc(10px / 4)") equals `2.5`
- a percentage that is not a whole pixel stays fractional: 12.5% of 200px is 25px, and 1% is 2px, so 1.5% is 3px
   - Expected: _read("calc(1.5%)") equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps fractional precision through division and percentages")
step("100% of 200px divided by 3 is 66.667px — an integer division would truncate this to 66 and shift a layout by two thirds of a pixel")
expect(_read("calc(100% / 3)")).to_equal("66.667")
step("10px / 4 is 2.5px, not 2px")
expect(_read("calc(10px / 4)")).to_equal("2.5")
step("a percentage that is not a whole pixel stays fractional: 12.5% of 200px is 25px, and 1% is 2px, so 1.5% is 3px")
expect(_read("calc(1.5%)")).to_equal("3.0")
```

</details>

#### reads a leading minus as a sign rather than as subtraction

- reads a leading minus as a sign rather than as subtraction
- calc(-10px + 30px) starts with a signed number and totals 20px
   - Expected: _read("calc(-10px + 30px)") equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a leading minus as a sign rather than as subtraction")
step("calc(-10px + 30px) starts with a signed number and totals 20px")
expect(_read("calc(-10px + 30px)")).to_equal("20.0")
```

</details>

### invalid length input

#### rejects multiplication where both operands carry a unit

- rejects multiplication where both operands carry a unit
- 10px * 5px would be an area; CSS has no unit for px squared, so at least one operand of * must be a plain number
   - Expected: r.ok is false
- the failure carries a reason rather than an empty string
   - Expected: r.error.len() > 0 is true
- a percentage counts as a unit for this rule too
   - Expected: _read("calc(50% * 2em)") equals `invalid`
- the legal direction still works: 10px * 5 is 50px
   - Expected: _read("calc(10px * 5)") equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects multiplication where both operands carry a unit")
step("10px * 5px would be an area; CSS has no unit for px squared, so at least one operand of * must be a plain number")
val r = parse_length_px("calc(10px * 5px)", _ctx())
expect(r.ok).to_equal(false)
step("the failure carries a reason rather than an empty string")
expect(r.error.len() > 0).to_equal(true)
step("a percentage counts as a unit for this rule too")
expect(_read("calc(50% * 2em)")).to_equal("invalid")
step("the legal direction still works: 10px * 5 is 50px")
expect(_read("calc(10px * 5)")).to_equal("50.0")
```

</details>

#### rejects division by anything that carries a unit

- rejects division by anything that carries a unit
- 10px / 5px would be a unitless ratio; CSS requires the divisor of / to be a plain number
   - Expected: _read("calc(10px / 5px)") equals `invalid`
- dividing by a percentage is rejected for the same reason
   - Expected: _read("calc(10px / 50%)") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects division by anything that carries a unit")
step("10px / 5px would be a unitless ratio; CSS requires the divisor of / to be a plain number")
expect(_read("calc(10px / 5px)")).to_equal("invalid")
step("dividing by a percentage is rejected for the same reason")
expect(_read("calc(10px / 50%)")).to_equal("invalid")
```

</details>

#### rejects division by zero instead of producing an infinity

- rejects division by zero instead of producing an infinity
- 10px / 0 has no pixel value; an infinity would propagate silently
   - Expected: _read("calc(10px / 0)") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects division by zero instead of producing an infinity")
step("10px / 0 has no pixel value; an infinity would propagate silently")
expect(_read("calc(10px / 0)")).to_equal("invalid")
```

</details>

#### rejects adding a length to a plain number

- rejects adding a length to a plain number
- 1px + 2 has no meaning: the 2 is dimensionless and CSS does not assume px for it
   - Expected: _read("calc(1px + 2)") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects adding a length to a plain number")
step("1px + 2 has no meaning: the 2 is dimensionless and CSS does not assume px for it")
expect(_read("calc(1px + 2)")).to_equal("invalid")
```

</details>

#### rejects + and - without whitespace on both sides

- rejects + and - without whitespace on both sides
- CSS requires whitespace around additive operators inside calc(). In calc(100%-20px) the -20px is a signed number, leaving two values with no operator between them
   - Expected: _read("calc(100%-20px)") equals `invalid`
- whitespace on one side only is the same error
   - Expected: _read("calc(100% -20px)") equals `invalid`
- with whitespace on both sides it resolves: 200px - 20px is 180px
   - Expected: _read("calc(100% - 20px)") equals `180.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects + and - without whitespace on both sides")
step("CSS requires whitespace around additive operators inside calc(). In calc(100%-20px) the -20px is a signed number, leaving two values with no operator between them")
expect(_read("calc(100%-20px)")).to_equal("invalid")
step("whitespace on one side only is the same error")
expect(_read("calc(100% -20px)")).to_equal("invalid")
step("with whitespace on both sides it resolves: 200px - 20px is 180px")
expect(_read("calc(100% - 20px)")).to_equal("180.0")
```

</details>

#### rejects malformed expressions rather than salvaging a prefix

- rejects malformed expressions rather than salvaging a prefix
- an unbalanced parenthesis is not a complete expression
   - Expected: _read("calc(10px + 5px") equals `invalid`
- an empty calc() has no value
   - Expected: _read("calc()") equals `invalid`
- a dangling operator has no right-hand side
   - Expected: _read("calc(10px +)") equals `invalid`
- trailing junk must not be discarded in favour of the 10px prefix
   - Expected: _read("10px 20px") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed expressions rather than salvaging a prefix")
step("an unbalanced parenthesis is not a complete expression")
expect(_read("calc(10px + 5px")).to_equal("invalid")
step("an empty calc() has no value")
expect(_read("calc()")).to_equal("invalid")
step("a dangling operator has no right-hand side")
expect(_read("calc(10px +)")).to_equal("invalid")
step("trailing junk must not be discarded in favour of the 10px prefix")
expect(_read("10px 20px")).to_equal("invalid")
```

</details>

#### rejects unknown units, unsupported functions and empty input

- rejects unknown units, unsupported functions and empty input
- furlongs are not a CSS unit
   - Expected: _read("10furlong") equals `invalid`
- min()/max()/clamp() are not implemented, so they fail rather than resolving to one of their arguments
   - Expected: _read("min(10px, 20px)") equals `invalid`
- var() is not resolved here either
   - Expected: _read("var(--gap)") equals `invalid`
- an empty value is not a length
   - Expected: _read("") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unknown units, unsupported functions and empty input")
step("furlongs are not a CSS unit")
expect(_read("10furlong")).to_equal("invalid")
step("min()/max()/clamp() are not implemented, so they fail rather than resolving to one of their arguments")
expect(_read("min(10px, 20px)")).to_equal("invalid")
step("var() is not resolved here either")
expect(_read("var(--gap)")).to_equal("invalid")
step("an empty value is not a length")
expect(_read("")).to_equal("invalid")
```

</details>

#### rejects a non-zero number with no unit

- rejects a non-zero number with no unit
- CSS accepts a bare 0 as a length but not a bare 5 — accepting it as 5px is exactly the plausible-wrong-value trap
   - Expected: _read("5") equals `invalid`
- the same rule applies to a calc() that reduces to a bare number: 2 * 3 is 6, which is dimensionless and so is not a length
   - Expected: _read("calc(2 * 3)") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-zero number with no unit")
step("CSS accepts a bare 0 as a length but not a bare 5 — accepting it as 5px is exactly the plausible-wrong-value trap")
expect(_read("5")).to_equal("invalid")
step("the same rule applies to a calc() that reduces to a bare number: 2 * 3 is 6, which is dimensionless and so is not a length")
expect(_read("calc(2 * 3)")).to_equal("invalid")
```

</details>

### parse_calc_px and is_calc

#### accepts only the function form

- accepts only the function form
- parse_calc_px resolves a calc(): 2em + 8px is 32 + 8 = 40px
   - Expected: good.ok is true
- a bare dimension is rejected by this entry point
   - Expected: parse_calc_px("10px", _ctx()).ok is false
- is_calc reports the form without evaluating it
   - Expected: is_calc("calc(1px + 1px)") is true
   - Expected: is_calc("10px") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only the function form")
step("parse_calc_px resolves a calc(): 2em + 8px is 32 + 8 = 40px")
val good = parse_calc_px("calc(2em + 8px)", _ctx())
expect(good.ok).to_equal(true)
step("a bare dimension is rejected by this entry point")
expect(parse_calc_px("10px", _ctx()).ok).to_equal(false)
step("is_calc reports the form without evaluating it")
expect(is_calc("calc(1px + 1px)")).to_equal(true)
expect(is_calc("10px")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `0e25639e225ac040b9d374a06fffc305572d2cca90a19d72fe772fb9345d9d53`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e25639e225ac040b9d374a06fffc305572d2cca90a19d72fe772fb9345d9d53`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e25639e225ac040b9d374a06fffc305572d2cca90a19d72fe772fb9345d9d53`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/css/length_spec.spl
mirror: doc/06_spec/01_unit/lib/common/css/length_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/css/length_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/css/length_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/css/length_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves absolute units by their fixed ratio to the CSS pixel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/css/length_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves em against the element font and rem against the root font' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/css/length_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves viewport units against the 800x600 viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
