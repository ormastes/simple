# Simple Web Html Layout Renderer Foundation Gradient Specification

> Tests covering parse_linear_gradient_color angle-token regression (GAP-2 bug), parse_gradient_angle_deg, parse_gradient_stops N-stop upgrade, radial-gradient detection and N-stop parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Html Layout Renderer Foundation Gradient Specification

## Scenarios

### parse_linear_gradient_color angle-token regression (GAP-2 bug)

#### does not let a numeric angle token shift the color stop index

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not let a numeric angle token shift the color stop index
   - Expected: parse_linear_gradient_color(css, 0) equals `RED`
   - Expected: parse_linear_gradient_color(css, 1) equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not let a numeric angle token shift the color stop index")
val css = "linear-gradient(45deg, #ff0000, #0000ff)"
# Before the fix: target=0 returned parse_color_any("45deg") == 0,
# and target=1 returned the FIRST color (red) instead of the second.
expect(parse_linear_gradient_color(css, 0)).to_equal(RED)
expect(parse_linear_gradient_color(css, 1)).to_equal(BLUE)
```

</details>

#### still shifts on other numeric angle units (grad/rad/turn)

- still shifts on other numeric angle units (grad/rad/turn)
   - Expected: parse_linear_gradient_color("linear-gradient(0.5turn, #ff0000, #0000ff)", 0) equals `RED`
   - Expected: parse_linear_gradient_color("linear-gradient(200grad, #ff0000, #0000ff)", 0) equals `RED`
   - Expected: parse_linear_gradient_color("linear-gradient(1rad, #ff0000, #0000ff)", 0) equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still shifts on other numeric angle units (grad/rad/turn)")
expect(parse_linear_gradient_color("linear-gradient(0.5turn, #ff0000, #0000ff)", 0)).to_equal(RED)
expect(parse_linear_gradient_color("linear-gradient(200grad, #ff0000, #0000ff)", 0)).to_equal(RED)
expect(parse_linear_gradient_color("linear-gradient(1rad, #ff0000, #0000ff)", 0)).to_equal(RED)
```

</details>

#### keeps working with no direction token at all

- keeps working with no direction token at all
   - Expected: parse_linear_gradient_color(css, 0) equals `RED`
   - Expected: parse_linear_gradient_color(css, 1) equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps working with no direction token at all")
val css = "linear-gradient(#ff0000, #0000ff)"
expect(parse_linear_gradient_color(css, 0)).to_equal(RED)
expect(parse_linear_gradient_color(css, 1)).to_equal(BLUE)
```

</details>

#### keeps working with the pre-existing keyword direction form

- keeps working with the pre-existing keyword direction form
   - Expected: parse_linear_gradient_color(css, 0) equals `RED`
   - Expected: parse_linear_gradient_color(css, 1) equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps working with the pre-existing keyword direction form")
val css = "linear-gradient(to bottom, #ff0000, #0000ff)"
expect(parse_linear_gradient_color(css, 0)).to_equal(RED)
expect(parse_linear_gradient_color(css, 1)).to_equal(BLUE)
```

</details>

### parse_gradient_angle_deg

#### reads a numeric degree angle

- reads a numeric degree angle
   - Expected: parse_gradient_angle_deg("linear-gradient(45deg, #ff0000, #0000ff)") equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads a numeric degree angle")
expect(parse_gradient_angle_deg("linear-gradient(45deg, #ff0000, #0000ff)")).to_equal(45)
```

</details>

#### reads keyword directions

- reads keyword directions
   - Expected: parse_gradient_angle_deg("linear-gradient(to top, #ff0000, #0000ff)") equals `0`
   - Expected: parse_gradient_angle_deg("linear-gradient(to right, #ff0000, #0000ff)") equals `90`
   - Expected: parse_gradient_angle_deg("linear-gradient(to left, #ff0000, #0000ff)") equals `270`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads keyword directions")
expect(parse_gradient_angle_deg("linear-gradient(to top, #ff0000, #0000ff)")).to_equal(0)
expect(parse_gradient_angle_deg("linear-gradient(to right, #ff0000, #0000ff)")).to_equal(90)
expect(parse_gradient_angle_deg("linear-gradient(to left, #ff0000, #0000ff)")).to_equal(270)
```

</details>

#### defaults to 180 (CSS 'to bottom') with no direction token

- defaults to 180 (CSS 'to bottom') with no direction token
   - Expected: parse_gradient_angle_deg("linear-gradient(#ff0000, #0000ff)") equals `180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults to 180 (CSS 'to bottom') with no direction token")
expect(parse_gradient_angle_deg("linear-gradient(#ff0000, #0000ff)")).to_equal(180)
```

</details>

### parse_gradient_stops N-stop upgrade

#### parses 3 stops with implicit even spacing

- parses 3 stops with implicit even spacing
   - Expected: stops.len() equals `3`
   - Expected: stops[0].color equals `RED`
   - Expected: stops[0].pos_permille equals `0`
   - Expected: stops[1].color equals `GREEN`
   - Expected: stops[1].pos_permille equals `500`
   - Expected: stops[2].color equals `BLUE`
   - Expected: stops[2].pos_permille equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses 3 stops with implicit even spacing")
val stops = parse_gradient_stops("linear-gradient(180deg, #ff0000, #00ff00, #0000ff)")
expect(stops.len()).to_equal(3)
expect(stops[0].color).to_equal(RED)
expect(stops[0].pos_permille).to_equal(0)
expect(stops[1].color).to_equal(GREEN)
expect(stops[1].pos_permille).to_equal(500)
expect(stops[2].color).to_equal(BLUE)
expect(stops[2].pos_permille).to_equal(1000)
```

</details>

#### honors explicit percentage stop positions

- honors explicit percentage stop positions
   - Expected: stops.len() equals `3`
   - Expected: stops[0].pos_permille equals `100`
   - Expected: stops[1].pos_permille equals `500`
   - Expected: stops[2].pos_permille equals `900`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("honors explicit percentage stop positions")
val stops = parse_gradient_stops("linear-gradient(#ff0000 10%, #00ff00 50%, #0000ff 90%)")
expect(stops.len()).to_equal(3)
expect(stops[0].pos_permille).to_equal(100)
expect(stops[1].pos_permille).to_equal(500)
expect(stops[2].pos_permille).to_equal(900)
```

</details>

#### does not misparse an angle token as a 4th stop

- does not misparse an angle token as a 4th stop
   - Expected: stops.len() equals `3`
   - Expected: stops[0].color equals `RED`
   - Expected: stops[2].color equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not misparse an angle token as a 4th stop")
val stops = parse_gradient_stops("linear-gradient(45deg, #ff0000, #00ff00, #0000ff)")
expect(stops.len()).to_equal(3)
expect(stops[0].color).to_equal(RED)
expect(stops[2].color).to_equal(BLUE)
```

</details>

### radial-gradient detection and N-stop parsing

#### distinguishes radial from linear

- distinguishes radial from linear
   - Expected: is_radial_gradient("radial-gradient(#ff0000, #00ff00)") is true
   - Expected: is_radial_gradient("linear-gradient(#ff0000, #00ff00)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes radial from linear")
expect(is_radial_gradient("radial-gradient(#ff0000, #00ff00)")).to_equal(true)
expect(is_radial_gradient("linear-gradient(#ff0000, #00ff00)")).to_equal(false)
```

</details>

#### parses radial stops with no shape/position prefix

- parses radial stops with no shape/position prefix
   - Expected: stops.len() equals `3`
   - Expected: stops[0].color equals `RED`
   - Expected: stops[1].color equals `GREEN`
   - Expected: stops[2].color equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses radial stops with no shape/position prefix")
val stops = parse_gradient_stops("radial-gradient(#ff0000, #00ff00, #0000ff)")
expect(stops.len()).to_equal(3)
expect(stops[0].color).to_equal(RED)
expect(stops[1].color).to_equal(GREEN)
expect(stops[2].color).to_equal(BLUE)
```

</details>

#### skips a leading shape/position prefix

- skips a leading shape/position prefix
   - Expected: stops.len() equals `2`
   - Expected: stops[0].color equals `RED`
   - Expected: stops[1].color equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips a leading shape/position prefix")
val stops = parse_gradient_stops("radial-gradient(circle at center, #ff0000, #0000ff)")
expect(stops.len()).to_equal(2)
expect(stops[0].color).to_equal(RED)
expect(stops[1].color).to_equal(BLUE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse_linear_gradient_color angle-token regression (GAP-2 bug), parse_gradient_angle_deg, parse_gradient_stops N-stop upgrade, radial-gradient detection and N-stop parsing.
- parse_linear_gradient_color angle-token regression (GAP-2 bug)
- parse_gradient_angle_deg
- parse_gradient_stops N-stop upgrade
- radial-gradient detection and N-stop parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `3af3302151754144fea65b9dd70d84ee7c5899adee28fc38e7eede8ae818a83f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3af3302151754144fea65b9dd70d84ee7c5899adee28fc38e7eede8ae818a83f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3af3302151754144fea65b9dd70d84ee7c5899adee28fc38e7eede8ae818a83f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not let a numeric angle token shift the color stop index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still shifts on other numeric angle units (grad/rad/turn)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps working with no direction token at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
