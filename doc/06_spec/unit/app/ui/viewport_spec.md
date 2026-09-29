# Viewport Specification

> Tests covering Viewport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Viewport Specification

## Scenarios

### Viewport

#### creates default viewport

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates default viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default viewport")
val vp = default_viewport()
expect vp.width to_equal 80
expect vp.height to_equal 24
expect vp.active_backend to_equal "none"
```

</details>

#### creates custom viewport

- creates custom viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates custom viewport")
val vp = new_viewport(1920, 1080, "tauri")
expect vp.width to_equal 1920
expect vp.height to_equal 1080
expect vp.active_backend to_equal "tauri"
```

</details>

#### computes area

- computes area


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes area")
val vp = new_viewport(80, 24, "tui")
expect vp.area() to_equal 1920
```

</details>

#### detects active state

- detects active state


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects active state")
val vp1 = default_viewport()
expect vp1.is_active() to_equal false
val vp2 = new_viewport(80, 24, "tui")
expect vp2.is_active() to_equal true
```

</details>

#### describes itself

- describes itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes itself")
val vp = new_viewport(120, 40, "electron")
expect vp.describe() to_equal "120x40 (electron)"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/viewport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Viewport.
- Viewport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `1637c0b5733f670bc10e4b8ba6bea3f54967586275ea8b11d3bab4b0f2d2affd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1637c0b5733f670bc10e4b8ba6bea3f54967586275ea8b11d3bab4b0f2d2affd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1637c0b5733f670bc10e4b8ba6bea3f54967586275ea8b11d3bab4b0f2d2affd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/viewport_spec.spl
mirror: doc/06_spec/unit/app/ui/viewport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/viewport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/viewport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/viewport_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/viewport_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates custom viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/viewport_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes area' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
