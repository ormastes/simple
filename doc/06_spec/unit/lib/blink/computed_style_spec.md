# Blink ComputedStyle Specification

> Tests for the Blink-style ComputedStyle stub — the resolved CSS property bag for a DOM element after style cascade. Covers default values, visibility, positioning, margin totals, and block-level classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink ComputedStyle Specification

Tests for the Blink-style ComputedStyle stub — the resolved CSS property bag for a DOM element after style cascade. Covers default values, visibility, positioning, margin totals, and block-level classification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/unit/lib/blink/computed_style_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style ComputedStyle stub — the resolved CSS property bag
for a DOM element after style cascade. Covers default values, visibility,
positioning, margin totals, and block-level classification.

## Scenarios

### computed_style_default

#### display is Inline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- display is Inline
   - Expected: is_inline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("display is Inline")
val style = computed_style_default()
val is_inline = style.display == Display.Inline
expect(is_inline).to_equal(true)
```

</details>

#### is_visible returns true

- is_visible returns true
   - Expected: style.is_visible() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_visible returns true")
val style = computed_style_default()
expect(style.is_visible()).to_equal(true)
```

</details>

#### is_positioned returns false

- is_positioned returns false
   - Expected: style.is_positioned() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_positioned returns false")
val style = computed_style_default()
expect(style.is_positioned()).to_equal(false)
```

</details>

### is_visible

#### opacity 0 returns false

- opacity 0 returns false
   - Expected: style.is_visible() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opacity 0 returns false")
val style = computed_style_default()
style.opacity = 0.0
expect(style.is_visible()).to_equal(false)
```

</details>

### is_block_level

#### Block display returns true, Inline returns false

- Block display returns true, Inline returns false
   - Expected: style.is_block_level() is true
   - Expected: style.is_block_level() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Block display returns true, Inline returns false")
val style = computed_style_default()
style.display = Display.Block
expect(style.is_block_level()).to_equal(true)
style.display = Display.Inline
expect(style.is_block_level()).to_equal(false)
```

</details>

### total_margin_horizontal

#### sum of left + right margin

- sum of left + right margin
   - Expected: style.total_margin_horizontal() equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum of left + right margin")
val style = computed_style_default()
style.margin_left = Length(value: 12.0, unit: "px")
style.margin_right = Length(value: 8.0, unit: "px")
expect(style.total_margin_horizontal()).to_equal(20.0)
expect(style.total_margin_horizontal()).to_be_greater_than(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `a0ac107feb59694b06b5ba8d5a198bbed6584c7806880829ea0925adabb75c29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0ac107feb59694b06b5ba8d5a198bbed6584c7806880829ea0925adabb75c29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0ac107feb59694b06b5ba8d5a198bbed6584c7806880829ea0925adabb75c29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/blink/computed_style_spec.spl
mirror: doc/06_spec/unit/lib/blink/computed_style_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/computed_style_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/computed_style_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/computed_style_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/computed_style_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'display is Inline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/computed_style_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_visible returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/computed_style_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_positioned returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
