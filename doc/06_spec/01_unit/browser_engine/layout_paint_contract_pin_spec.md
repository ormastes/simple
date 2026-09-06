# Layout Paint Contract Pin Specification

> Tests covering BeLayoutBox real contract (repro class for _paint_box defect), layout_paint surviving surface (generalization).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Paint Contract Pin Specification

## Scenarios

### BeLayoutBox real contract (repro class for _paint_box defect)

#### carries node_id, not a node object field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries node_id, not a node object field
   - Expected: b.node_id >= -1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries node_id, not a node object field")
val b = probe_box()
expect(b.node_id >= -1).to_equal(true)
```

</details>

#### content geometry is exposed as methods computed from box model

- content geometry is exposed as methods computed from box model
   - Expected: b.content_x() equals `10.0 + 4.0 + 2.0`
   - Expected: b.content_y() equals `20.0 + 3.0 + 2.0`
   - Expected: b.content_width() equals `100.0 - 4.0 - 2.0 - 2.0 * 2.0`
   - Expected: b.content_height() equals `50.0 - 3.0 - 1.0 - 2.0 * 2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("content geometry is exposed as methods computed from box model")
val b = probe_box()
expect(b.content_x()).to_equal(10.0 + 4.0 + 2.0)
expect(b.content_y()).to_equal(20.0 + 3.0 + 2.0)
expect(b.content_width()).to_equal(100.0 - 4.0 - 2.0 - 2.0 * 2.0)
expect(b.content_height()).to_equal(50.0 - 3.0 - 1.0 - 2.0 * 2.0)
```

</details>

### layout_paint surviving surface (generalization)

#### opacity 1.0 is identity

- opacity 1.0 is identity
   - Expected: _apply_opacity(0xFF112233, 1.0) equals `0xFF112233`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opacity 1.0 is identity")
expect(_apply_opacity(0xFF112233, 1.0)).to_equal(0xFF112233)
```

</details>

#### opacity 0.0 clears alpha only

- opacity 0.0 clears alpha only
   - Expected: _apply_opacity(0xFF112233, 0.0) equals `0x00112233`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opacity 0.0 clears alpha only")
expect(_apply_opacity(0xFF112233, 0.0)).to_equal(0x00112233)
```

</details>

#### partial opacity scales alpha and preserves rgb

- partial opacity scales alpha and preserves rgb
   - Expected: _apply_opacity(0x80ABCDEF, 0.5) & 0x00FFFFFF equals `0x00ABCDEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("partial opacity scales alpha and preserves rgb")
expect(_apply_opacity(0x80ABCDEF, 0.5) & 0x00FFFFFF).to_equal(0x00ABCDEF)
```

</details>

#### zero-alpha input stays zero-alpha under partial opacity

- zero-alpha input stays zero-alpha under partial opacity
   - Expected: _apply_opacity(0x00445566, 0.5) equals `0x00445566`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-alpha input stays zero-alpha under partial opacity")
expect(_apply_opacity(0x00445566, 0.5)).to_equal(0x00445566)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BeLayoutBox real contract (repro class for _paint_box defect), layout_paint surviving surface (generalization).
- BeLayoutBox real contract (repro class for _paint_box defect)
- layout_paint surviving surface (generalization)

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

- Canonical SPipe generation for source `90418ee0b539f9c2c19efa3c95418a8ac0f073d281605e54df9e99337a7486ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90418ee0b539f9c2c19efa3c95418a8ac0f073d281605e54df9e99337a7486ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90418ee0b539f9c2c19efa3c95418a8ac0f073d281605e54df9e99337a7486ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/layout_paint_contract_pin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/layout_paint_contract_pin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/layout_paint_contract_pin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries node_id, not a node object field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'content geometry is exposed as methods computed from box model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opacity 1.0 is identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
