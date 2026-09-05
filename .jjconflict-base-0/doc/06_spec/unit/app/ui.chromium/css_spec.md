# Css Specification

> Tests covering Chromium CSS subset — flex-flow shorthand, Chromium CSS subset — hsl/hsla color parsing, Chromium CSS subset — currentColor keyword, Chromium CSS subset — DesktopShell glass-theme properties.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Specification

## Scenarios

### Chromium CSS subset — flex-flow shorthand

#### expands 'row wrap' into flex-direction=row + flex-wrap=wrap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- expands 'row wrap' into flex-direction=row + flex-wrap=wrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands 'row wrap' into flex-direction=row + flex-wrap=wrap")
val out = expand_flex_flow("row wrap")
expect(out.len() == 2).to_be_true()
expect(css_decls_contain(out, "flex-direction", "row")).to_be_true()
expect(css_decls_contain(out, "flex-wrap", "wrap")).to_be_true()
```

</details>

#### expands bare 'column-reverse' with default nowrap

- expands bare 'column-reverse' with default nowrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands bare 'column-reverse' with default nowrap")
val out = expand_flex_flow("column-reverse")
expect(out.len() == 2).to_be_true()
expect(css_decls_contain(out, "flex-direction", "column-reverse")).to_be_true()
expect(css_decls_contain(out, "flex-wrap", "nowrap")).to_be_true()
```

</details>

#### expands 'wrap-reverse row' (order-independent)

- expands 'wrap-reverse row' (order-independent)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands 'wrap-reverse row' (order-independent)")
val out = expand_flex_flow("wrap-reverse row")
expect(out.len() == 2).to_be_true()
expect(css_decls_contain(out, "flex-direction", "row")).to_be_true()
expect(css_decls_contain(out, "flex-wrap", "wrap-reverse")).to_be_true()
```

</details>

### Chromium CSS subset — hsl/hsla color parsing

#### parses hsl(0, 100%, 50%) as pure red

- parses hsl(0, 100%, 50%) as pure red


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hsl(0, 100%, 50%) as pure red")
val c = parse_color_value("hsl(0, 100%, 50%)")
# RGBA packed as 0xRRGGBBAA — red = 0xFF0000FF
expect(c == 0xFF0000FF).to_be_true()
```

</details>

#### parses hsl(120, 100%, 50%) as pure green

- parses hsl(120, 100%, 50%) as pure green


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hsl(120, 100%, 50%) as pure green")
val c = parse_color_value("hsl(120, 100%, 50%)")
expect(c == 0x00FF00FF).to_be_true()
```

</details>

#### parses hsl(240, 100%, 50%) as pure blue

- parses hsl(240, 100%, 50%) as pure blue


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hsl(240, 100%, 50%) as pure blue")
val c = parse_color_value("hsl(240, 100%, 50%)")
expect(c == 0x0000FFFF).to_be_true()
```

</details>

#### parses hsla(0, 0%, 0%, 1.0) as opaque black

- parses hsla(0, 0%, 0%, 1.0) as opaque black


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hsla(0, 0%, 0%, 1.0) as opaque black")
val c = parse_color_value("hsla(0, 0%, 0%, 1.0)")
expect(c == 0x000000FF).to_be_true()
```

</details>

#### parses hsl(0, 0%, 100%) as white

- parses hsl(0, 0%, 100%) as white


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hsl(0, 0%, 100%) as white")
val c = parse_color_value("hsl(0, 0%, 100%)")
expect(c == 0xFFFFFFFF).to_be_true()
```

</details>

### Chromium CSS subset — currentColor keyword

#### resolves border-color: currentColor to the element's color

- resolves border-color: currentColor to the element's color


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves border-color: currentColor to the element's color")
var node = BeDomNode.element("div")
# Establish the element's color first.
node.set_style("color", "#FF00FFFF")  # magenta
node.set_style("border-width", "2px")
node.set_style("border-color", "currentColor")
expect(be_dom_get_border_color(node).value == 0xFF00FFFF).to_be_true()
```

</details>

#### accepts the mixed-case spelling 'currentColor'

- accepts the mixed-case spelling 'currentColor'


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the mixed-case spelling 'currentColor'")
var node = BeDomNode.element("div")
node.set_style("color", "#112233FF")
node.set_style("border-color", "currentColor")
expect(be_dom_get_border_color(node).value == 0x112233FF).to_be_true()
```

</details>

### Chromium CSS subset — DesktopShell glass-theme properties

#### accepts the full panel property set without losing values

- accepts the full panel property set without losing values


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the full panel property set without losing values")
var node = BeDomNode.element("div")
node.set_style("display", "flex")
node.set_style("flex-direction", "column")
node.set_style("gap", "8px")
node.set_style("padding", "10px")
node.set_style("background-color", "rgba(30,30,35,0.72)")
node.set_style("border-width", "1px")
node.set_style("border-color", "rgba(255,255,255,0.08)")
node.set_style("border-radius", "20px")
node.set_style("color", "#F5F5F7FF")
val s = node.style
expect(be_dom_get_display(node) == "flex").to_be_true()
expect(css_get_flex_direction(s) == "column").to_be_true()
expect(css_get_gap(s).value == 8).to_be_true()
expect(be_dom_get_padding_top(node).value == 10).to_be_true()
expect(be_dom_get_padding_left(node).value == 10).to_be_true()
expect(be_dom_get_border_width(node).value == 1).to_be_true()
expect(be_dom_get_border_radius(node).value == 20).to_be_true()
```

</details>

#### stores display: flow-root and display: contents as freeform values

- stores display: flow-root and display: contents as freeform values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores display: flow-root and display: contents as freeform values")
# These are not emitted by widget_to_dom for DesktopShell today
# (waived per M3 acceptance), but set_style must not panic if a
# future widget set-style path feeds them in.
var node1 = BeDomNode.element("div")
node1.set_style("display", "flow-root")
expect(be_dom_get_display(node1) == "flow-root").to_be_true()

var node2 = BeDomNode.element("div")
node2.set_style("display", "contents")
expect(be_dom_get_display(node2) == "contents").to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/css_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium CSS subset — flex-flow shorthand, Chromium CSS subset — hsl/hsla color parsing, Chromium CSS subset — currentColor keyword, Chromium CSS subset — DesktopShell glass-theme properties.
- Chromium CSS subset — flex-flow shorthand
- Chromium CSS subset — hsl/hsla color parsing
- Chromium CSS subset — currentColor keyword
- Chromium CSS subset — DesktopShell glass-theme properties

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `e748940b90f8d3021ef92f7841b17f8a08bf6aeb92e7d6296ad9e4fbca9febac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e748940b90f8d3021ef92f7841b17f8a08bf6aeb92e7d6296ad9e4fbca9febac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e748940b90f8d3021ef92f7841b17f8a08bf6aeb92e7d6296ad9e4fbca9febac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/css_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/css_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/css_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/css_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/css_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands 'row wrap' into flex-direction=row + flex-wrap=wrap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/css_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands bare 'column-reverse' with default nowrap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/css_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands 'wrap-reverse row' (order-independent)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
