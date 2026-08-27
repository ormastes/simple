# Brush Specification

> Tests covering BrushConfig — default_brush, BrushConfig — default_eraser, BrushConfig — effective_size with pressure, BrushConfig — effective_opacity with pressure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Brush Specification

## Scenarios

### BrushConfig — default_brush

#### default brush size is greater than 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- default brush size is greater than 0
   - Expected: b.size > 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default brush size is greater than 0")
val b = BrushConfig.default_brush()
expect(b.size > 0.0).to_equal(true)
```

</details>

#### default brush opacity is greater than 0

- default brush opacity is greater than 0
   - Expected: b.opacity > 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default brush opacity is greater than 0")
val b = BrushConfig.default_brush()
expect(b.opacity > 0.0).to_equal(true)
```

</details>

### BrushConfig — default_eraser

#### default eraser is a valid config with size greater than 0

- default eraser is a valid config with size greater than 0
   - Expected: e.size > 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default eraser is a valid config with size greater than 0")
val e = BrushConfig.default_eraser()
expect(e.size > 0.0).to_equal(true)
```

</details>

#### default eraser opacity is greater than 0

- default eraser opacity is greater than 0
   - Expected: e.opacity > 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default eraser opacity is greater than 0")
val e = BrushConfig.default_eraser()
expect(e.opacity > 0.0).to_equal(true)
```

</details>

### BrushConfig — effective_size with pressure

#### pressure 0.5 reduces size when pressure_size is true

- pressure 0.5 reduces size when pressure_size is true
   - Expected: eff > half - 0.01 is true
   - Expected: eff < half + 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pressure 0.5 reduces size when pressure_size is true")
val b = BrushConfig.default_brush()
val eff = b.effective_size(0.5)
val half = b.size * 0.5
expect(eff > half - 0.01).to_equal(true)
expect(eff < half + 0.01).to_equal(true)
```

</details>

#### pressure has no effect when pressure_size is false

- pressure has no effect when pressure_size is false
   - Expected: eff > b.size - 0.01 is true
   - Expected: eff < b.size + 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pressure has no effect when pressure_size is false")
val b = BrushConfig.pencil()
val eff = b.effective_size(0.5)
expect(eff > b.size - 0.01).to_equal(true)
expect(eff < b.size + 0.01).to_equal(true)
```

</details>

### BrushConfig — effective_opacity with pressure

#### pressure 0.5 reduces opacity when pressure_opacity is true

- pressure 0.5 reduces opacity when pressure_opacity is true
   - Expected: eff > half - 0.01 is true
   - Expected: eff < half + 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pressure 0.5 reduces opacity when pressure_opacity is true")
val e = BrushConfig.default_eraser()
val eff = e.effective_opacity(0.5)
val half = e.opacity * 0.5
expect(eff > half - 0.01).to_equal(true)
expect(eff < half + 0.01).to_equal(true)
```

</details>

#### pressure has no effect when pressure_opacity is false

- pressure has no effect when pressure_opacity is false
   - Expected: eff > b.opacity - 0.01 is true
   - Expected: eff < b.opacity + 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pressure has no effect when pressure_opacity is false")
val b = BrushConfig.default_brush()
val eff = b.effective_opacity(0.5)
expect(eff > b.opacity - 0.01).to_equal(true)
expect(eff < b.opacity + 0.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/brush_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrushConfig — default_brush, BrushConfig — default_eraser, BrushConfig — effective_size with pressure, BrushConfig — effective_opacity with pressure.
- BrushConfig — default_brush
- BrushConfig — default_eraser
- BrushConfig — effective_size with pressure
- BrushConfig — effective_opacity with pressure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2598bc4c440edcb9e1b15bae78445af0c18deace24f3867517e44ded13c09b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2598bc4c440edcb9e1b15bae78445af0c18deace24f3867517e44ded13c09b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2598bc4c440edcb9e1b15bae78445af0c18deace24f3867517e44ded13c09b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/brush_spec.spl
mirror: doc/06_spec/03_system/gui/brush_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/brush_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/brush_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/brush_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default brush size is greater than 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/brush_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default brush opacity is greater than 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/brush_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default eraser is a valid config with size greater than 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
