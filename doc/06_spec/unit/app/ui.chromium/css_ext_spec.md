# Css Ext Specification

> Tests covering CSS ext — float / clear parsers, CSS ext — BoxShadow, CSS ext — Outline, CSS ext — calc() resolver, CSS ext — M8 milestone marker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Ext Specification

## Scenarios

### CSS ext — float / clear parsers

#### parses the CSS 2.1 float keyword set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the CSS 2.1 float keyword set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the CSS 2.1 float keyword set")
expect(parse_float_keyword("none") == 0).to_be_true()
expect(parse_float_keyword("left") == 1).to_be_true()
expect(parse_float_keyword("right") == 2).to_be_true()
```

</details>

#### parses the CSS Logical Properties float keywords

- parses the CSS Logical Properties float keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the CSS Logical Properties float keywords")
expect(parse_float_keyword("inline-start") == 3).to_be_true()
expect(parse_float_keyword("inline-end") == 4).to_be_true()
```

</details>

#### returns -1 for unknown float values

- returns -1 for unknown float values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for unknown float values")
expect(parse_float_keyword("wibble") == -1).to_be_true()
expect(parse_float_keyword("") == -1).to_be_true()
```

</details>

#### parses the full clear keyword set

- parses the full clear keyword set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the full clear keyword set")
expect(parse_clear_keyword("none") == 0).to_be_true()
expect(parse_clear_keyword("left") == 1).to_be_true()
expect(parse_clear_keyword("right") == 2).to_be_true()
expect(parse_clear_keyword("both") == 3).to_be_true()
expect(parse_clear_keyword("inline-start") == 4).to_be_true()
expect(parse_clear_keyword("inline-end") == 5).to_be_true()
```

</details>

#### returns -1 for unknown clear values

- returns -1 for unknown clear values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for unknown clear values")
expect(parse_clear_keyword("nope") == -1).to_be_true()
```

</details>

### CSS ext — BoxShadow

#### BoxShadow.none produces an invisible shadow

- BoxShadow.none produces an invisible shadow


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BoxShadow.none produces an invisible shadow")
val shadow = BoxShadow.none()
expect(not shadow.is_visible()).to_be_true()
expect(shadow.inset == false).to_be_true()
```

</details>

#### BoxShadow.new captures offsets / blur / spread / colour

- BoxShadow.new captures offsets / blur / spread / colour


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BoxShadow.new captures offsets / blur / spread / colour")
val shadow = BoxShadow.new(4, 6, 8, 2, 0xFF112233, false)
expect(shadow.offset_x_px == 4).to_be_true()
expect(shadow.offset_y_px == 6).to_be_true()
expect(shadow.blur_px == 8).to_be_true()
expect(shadow.spread_px == 2).to_be_true()
expect(shadow.is_visible()).to_be_true()
```

</details>

#### fully transparent shadow is not visible

- fully transparent shadow is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fully transparent shadow is not visible")
val shadow = BoxShadow.new(4, 4, 0, 0, 0x00112233, false)
expect(not shadow.is_visible()).to_be_true()
```

</details>

#### inset flag is preserved

- inset flag is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inset flag is preserved")
val shadow = BoxShadow.new(1, 1, 2, 0, 0xFF000000, true)
expect(shadow.inset == true).to_be_true()
```

</details>

### CSS ext — Outline

#### parses the full outline-style keyword set

- parses the full outline-style keyword set


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the full outline-style keyword set")
expect(parse_outline_style("none") == 0).to_be_true()
expect(parse_outline_style("hidden") == 1).to_be_true()
expect(parse_outline_style("dotted") == 2).to_be_true()
expect(parse_outline_style("dashed") == 3).to_be_true()
expect(parse_outline_style("solid") == 4).to_be_true()
expect(parse_outline_style("double") == 5).to_be_true()
expect(parse_outline_style("groove") == 6).to_be_true()
expect(parse_outline_style("ridge") == 7).to_be_true()
expect(parse_outline_style("inset") == 8).to_be_true()
expect(parse_outline_style("outset") == 9).to_be_true()
```

</details>

#### returns -1 for unknown outline-style

- returns -1 for unknown outline-style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for unknown outline-style")
expect(parse_outline_style("") == -1).to_be_true()
expect(parse_outline_style("wobble") == -1).to_be_true()
```

</details>

#### Outline.none is invisible

- Outline.none is invisible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Outline.none is invisible")
val o = Outline.none()
expect(not o.is_visible()).to_be_true()
```

</details>

#### Outline.new captures width / style / colour / offset

- Outline.new captures width / style / colour / offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Outline.new captures width / style / colour / offset")
val o = Outline.new(3, 4, 0xFFFF0000, 2)
expect(o.width_px == 3).to_be_true()
expect(o.offset_px == 2).to_be_true()
expect(o.is_visible()).to_be_true()
```

</details>

#### outline-style: none suppresses the outline even with width

- outline-style: none suppresses the outline even with width


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline-style: none suppresses the outline even with width")
val o = Outline.new(5, 0, 0xFFFFFFFF, 0)
expect(not o.is_visible()).to_be_true()
```

</details>

#### zero width outline is invisible

- zero width outline is invisible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero width outline is invisible")
val o = Outline.new(0, 4, 0xFFFFFFFF, 0)
expect(not o.is_visible()).to_be_true()
```

</details>

#### transparent colour outline is invisible

- transparent colour outline is invisible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transparent colour outline is invisible")
val o = Outline.new(2, 4, 0x00FFFFFF, 0)
expect(not o.is_visible()).to_be_true()
```

</details>

### CSS ext — calc() resolver

#### calc_apply handles the four operators

- calc_apply handles the four operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_apply handles the four operators")
val a = calc_apply(CALC_OP_ADD, 10, 5)
expect(a.ok).to_be_true()
expect(a.pixels == 15).to_be_true()
val s = calc_apply(CALC_OP_SUB, 10, 5)
expect(s.pixels == 5).to_be_true()
val m = calc_apply(CALC_OP_MUL, 10, 5)
expect(m.pixels == 50).to_be_true()
val d = calc_apply(CALC_OP_DIV, 10, 5)
expect(d.pixels == 2).to_be_true()
```

</details>

#### calc_apply reports divide-by-zero as a failed CalcValue

- calc_apply reports divide-by-zero as a failed CalcValue


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_apply reports divide-by-zero as a failed CalcValue")
val dz = calc_apply(CALC_OP_DIV, 10, 0)
expect(not dz.ok).to_be_true()
```

</details>

#### calc_resolve evaluates a lone value

- calc_resolve evaluates a lone value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve evaluates a lone value")
val r = calc_resolve([42], [])
expect(r.ok).to_be_true()
expect(r.pixels == 42).to_be_true()
```

</details>

#### calc_resolve honours operator precedence (2 + 3 * 4 == 14)

- calc_resolve honours operator precedence (2 + 3 * 4 == 14)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve honours operator precedence (2 + 3 * 4 == 14)")
val r = calc_resolve([2, 3, 4], [CALC_OP_ADD, CALC_OP_MUL])
expect(r.ok).to_be_true()
expect(r.pixels == 14).to_be_true()
```

</details>

#### calc_resolve walks + / - left to right (10 - 3 + 2 == 9)

- calc_resolve walks + / - left to right (10 - 3 + 2 == 9)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve walks + / - left to right (10 - 3 + 2 == 9)")
val r = calc_resolve([10, 3, 2], [CALC_OP_SUB, CALC_OP_ADD])
expect(r.ok).to_be_true()
expect(r.pixels == 9).to_be_true()
```

</details>

#### calc_resolve evaluates chained multiplications

- calc_resolve evaluates chained multiplications


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve evaluates chained multiplications")
val r = calc_resolve([2, 3, 4], [CALC_OP_MUL, CALC_OP_MUL])
expect(r.ok).to_be_true()
expect(r.pixels == 24).to_be_true()
```

</details>

#### calc_resolve propagates divide-by-zero

- calc_resolve propagates divide-by-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve propagates divide-by-zero")
val r = calc_resolve([10, 0], [CALC_OP_DIV])
expect(not r.ok).to_be_true()
```

</details>

#### calc_resolve rejects mismatched operand / operator counts

- calc_resolve rejects mismatched operand / operator counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve rejects mismatched operand / operator counts")
val r = calc_resolve([1, 2], [])
expect(not r.ok).to_be_true()
```

</details>

#### calc_resolve rejects empty operand list

- calc_resolve rejects empty operand list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calc_resolve rejects empty operand list")
val r = calc_resolve([], [])
expect(not r.ok).to_be_true()
```

</details>

### CSS ext — M8 milestone marker

#### marker reports the milestone number

- marker reports the milestone number


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marker reports the milestone number")
expect(m8_marker() == 8).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/css_ext_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSS ext — float / clear parsers, CSS ext — BoxShadow, CSS ext — Outline, CSS ext — calc() resolver, CSS ext — M8 milestone marker.
- CSS ext — float / clear parsers
- CSS ext — BoxShadow
- CSS ext — Outline
- CSS ext — calc() resolver
- CSS ext — M8 milestone marker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `1e2ea75d54c0a2cd1cea38213f28b55cb483d2135afd5b0db2317f686eee2f05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e2ea75d54c0a2cd1cea38213f28b55cb483d2135afd5b0db2317f686eee2f05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e2ea75d54c0a2cd1cea38213f28b55cb483d2135afd5b0db2317f686eee2f05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/css_ext_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/css_ext_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/css_ext_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/css_ext_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/css_ext_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the CSS 2.1 float keyword set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/css_ext_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the CSS Logical Properties float keywords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/css_ext_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns -1 for unknown float values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
