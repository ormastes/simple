# Blink Length Resolution Specification

> `blink.values.length` is the bridge from an authored CSS length to the CSS pixel number blink's layout and paint stages consume. The arithmetic itself lives in `common.css.length`; what this module owns is the part that is specific to blink — which percentage basis each PROPERTY resolves against, and how a `ComputedStyle` `Length` re-enters the shared reader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Length Resolution Specification

`blink.values.length` is the bridge from an authored CSS length to the CSS pixel number blink's layout and paint stages consume. The arithmetic itself lives in `common.css.length`; what this module owns is the part that is specific to blink — which percentage basis each PROPERTY resolves against, and how a `ComputedStyle` `Length` re-enters the shared reader.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/values_length_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`blink.values.length` is the bridge from an authored CSS length to the CSS
pixel number blink's layout and paint stages consume. The arithmetic itself
lives in `common.css.length`; what this module owns is the part that is
specific to blink — which percentage basis each PROPERTY resolves against, and
how a `ComputedStyle` `Length` re-enters the shared reader.

The property-dependent basis is the interesting half. It is invisible in a
square containing block, so every example below uses a deliberately
non-square 400 x 100 CSS px containing block: an inline-axis basis and a
block-axis basis can then never be confused for one another.

Failure is propagated rather than absorbed. A percentage in a property that
has no basis, and an expression this engine does not implement, both report
`ok = false` so the caller drops the declaration — which is what CSS mandates
— instead of laying out against a substituted zero.

## Scenarios

### basis_for_property

#### resolves inline-axis properties against the containing block width

- resolves inline-axis properties against the containing block width
- the containing block is 400px wide, so width: 50% is 200px
   - Expected: _read("width", "50%") equals `200.0`
- left is an inline-axis offset and uses the same 400px basis
   - Expected: _read("left", "25%") equals `100.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves inline-axis properties against the containing block width")
step("the containing block is 400px wide, so width: 50% is 200px")
expect(_read("width", "50%")).to_equal("200.0")
step("left is an inline-axis offset and uses the same 400px basis")
expect(_read("left", "25%")).to_equal("100.0")
```

</details>

#### resolves block-axis properties against the containing block height

- resolves block-axis properties against the containing block height
- the containing block is 100px tall, so height: 50% is 50px
   - Expected: _read("height", "50%") equals `50.0`
- top is a block-axis offset and uses the same 100px basis
   - Expected: _read("top", "25%") equals `25.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves block-axis properties against the containing block height")
step("the containing block is 100px tall, so height: 50% is 50px")
expect(_read("height", "50%")).to_equal("50.0")
step("top is a block-axis offset and uses the same 100px basis")
expect(_read("top", "25%")).to_equal("25.0")
```

</details>

#### resolves vertical margins and padding against the INLINE size

- resolves vertical margins and padding against the INLINE size
- CSS resolves percentage margins and padding on ALL FOUR sides against the containing block's inline size — margin-top: 10% of a 400x100 block is 40px, NOT 10px
   - Expected: _read("margin-top", "10%") equals `40.0`
- padding-bottom follows the same counter-intuitive rule
   - Expected: _read("padding-bottom", "10%") equals `40.0`
- the horizontal sides agree, which is why this rule hides so well
   - Expected: _read("margin-left", "10%") equals `40.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves vertical margins and padding against the INLINE size")
step("CSS resolves percentage margins and padding on ALL FOUR sides against the containing block's inline size — margin-top: 10% of a 400x100 block is 40px, NOT 10px")
expect(_read("margin-top", "10%")).to_equal("40.0")
step("padding-bottom follows the same counter-intuitive rule")
expect(_read("padding-bottom", "10%")).to_equal("40.0")
step("the horizontal sides agree, which is why this rule hides so well")
expect(_read("margin-left", "10%")).to_equal("40.0")
```

</details>

#### resolves font-size percentages against the inherited font size

- resolves font-size percentages against the inherited font size
- the inherited font size is 16px, so font-size: 150% is 24px
   - Expected: _read("font-size", "150%") equals `24.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves font-size percentages against the inherited font size")
step("the inherited font size is 16px, so font-size: 150% is 24px")
expect(_read("font-size", "150%")).to_equal("24.0")
```

</details>

#### reports no basis for a property whose percentages it cannot resolve

- reports no basis for a property whose percentages it cannot resolve
- basis_for_property returns the -1.0 sentinel for an unhandled property
   - Expected: basis < 0.0 is true
- a percentage in that property fails rather than resolving to 0px
   - Expected: _read("border-top-width", "10%") equals `invalid`
- an absolute length in that same property still resolves
   - Expected: _read("border-top-width", "3px") equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no basis for a property whose percentages it cannot resolve")
step("basis_for_property returns the -1.0 sentinel for an unhandled property")
val basis = basis_for_property("border-top-width", 400.0, 100.0, 16.0)
expect(basis < 0.0).to_equal(true)
step("a percentage in that property fails rather than resolving to 0px")
expect(_read("border-top-width", "10%")).to_equal("invalid")
step("an absolute length in that same property still resolves")
expect(_read("border-top-width", "3px")).to_equal("3.0")
```

</details>

### resolve_authored_length

#### resolves the same calc() differently per property axis

- resolves the same calc() differently per property axis
- on width the 100% is the 400px inline size, so 400 - 20 = 380px
   - Expected: _read("width", "calc(100% - 20px)") equals `380.0`
- on height the same text means the 100px block size, so 100 - 20 = 80px
   - Expected: _read("height", "calc(100% - 20px)") equals `80.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the same calc() differently per property axis")
step("on width the 100% is the 400px inline size, so 400 - 20 = 380px")
expect(_read("width", "calc(100% - 20px)")).to_equal("380.0")
step("on height the same text means the 100px block size, so 100 - 20 = 80px")
expect(_read("height", "calc(100% - 20px)")).to_equal("80.0")
```

</details>

#### mixes font-relative and viewport units inside one expression

- mixes font-relative and viewport units inside one expression
- 2em of a 16px font is 32px and 1vw of an 800px viewport is 8px, so their sum is 40px
   - Expected: _read("width", "calc(2em + 1vw)") equals `40.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixes font-relative and viewport units inside one expression")
step("2em of a 16px font is 32px and 1vw of an 800px viewport is 8px, so their sum is 40px")
expect(_read("width", "calc(2em + 1vw)")).to_equal("40.0")
```

</details>

#### propagates a rejection instead of substituting a number

- propagates a rejection instead of substituting a number
- multiplying two lengths is invalid CSS and must not become a width
   - Expected: _read("width", "calc(10px * 5px)") equals `invalid`
- an unimplemented function fails rather than resolving to an argument
   - Expected: _read("width", "clamp(1px, 2px, 3px)") equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates a rejection instead of substituting a number")
step("multiplying two lengths is invalid CSS and must not become a width")
expect(_read("width", "calc(10px * 5px)")).to_equal("invalid")
step("an unimplemented function fails rather than resolving to an argument")
expect(_read("width", "clamp(1px, 2px, 3px)")).to_equal("invalid")
```

</details>

### resolve_length

#### resolves a split Length through the shared unit table

- resolves a split Length through the shared unit table
- Length(2.0, rem) with a 10px root font is 20px — the rem path used to yield 0 because the old to_px() understood only px
   - Expected: rem.ok is true
   - Expected: ((rem.px * 10.0) + 0.5) as i64 equals `200`
- a percentage Length uses the property basis: 25% of 400px is 100px
   - Expected: ((pct.px * 10.0) + 0.5) as i64 equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a split Length through the shared unit table")
step("Length(2.0, rem) with a 10px root font is 20px — the rem path used to yield 0 because the old to_px() understood only px")
val rem = resolve_length(Length(value: 2.0, unit: "rem"), _ctx("width"))
expect(rem.ok).to_equal(true)
expect(((rem.px * 10.0) + 0.5) as i64).to_equal(200)
step("a percentage Length uses the property basis: 25% of 400px is 100px")
val pct = resolve_length(Length(value: 25.0, unit: "%"), _ctx("width"))
expect(((pct.px * 10.0) + 0.5) as i64).to_equal(1000)
```

</details>

#### accepts a unitless zero but rejects a unitless non-zero

- accepts a unitless zero but rejects a unitless non-zero
- 0 with no unit is the one unitless length CSS allows
   - Expected: zero.ok is true
- 5 with no unit is not a length, and must not be read as 5px
   - Expected: bare.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a unitless zero but rejects a unitless non-zero")
step("0 with no unit is the one unitless length CSS allows")
val zero = resolve_length(Length(value: 0.0, unit: ""), _ctx("width"))
expect(zero.ok).to_equal(true)
step("5 with no unit is not a length, and must not be read as 5px")
val bare = resolve_length(Length(value: 5.0, unit: ""), _ctx("width"))
expect(bare.ok).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-UNIT-UNITLESS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2c62df2b482cb625136d03b013f645aba15a1bcc5e84f9add63b6d23af2c677`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2c62df2b482cb625136d03b013f645aba15a1bcc5e84f9add63b6d23af2c677`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2c62df2b482cb625136d03b013f645aba15a1bcc5e84f9add63b6d23af2c677`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/values_length_spec.spl
mirror: doc/06_spec/unit/lib/blink/values_length_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/values_length_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/values_length_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/values_length_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/values_length_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/values_length_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves inline-axis properties against the containing block width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/values_length_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves block-axis properties against the containing block height' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/values_length_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves vertical margins and padding against the INLINE size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
