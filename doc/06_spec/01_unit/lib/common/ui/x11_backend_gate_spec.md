# X11 Backend Gate Specification

> Tests covering X11-class backend readiness gate, feature coverage, event coverage, pixel coverage, WM property coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X11 Backend Gate Specification

## Scenarios

### X11-class backend readiness gate

### feature coverage

#### lists native WM features needed by a future Wine backend

- lists native WM features needed by a future Wine backend
   - Expected: required[0] equals `display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists native WM features needed by a future Wine backend")
val required = x11_backend_required_features()
expect(required.len()).to_be_greater_than(10)
expect(required[0]).to_equal("display")
```

</details>

#### reports the first missing X11-class renderer feature

- reports the first missing X11-class renderer feature
   - Expected: state equals `missing-wm-state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing X11-class renderer feature")
val state = x11_backend_gate("display screen window map-unmap configure surface damage clip expose present input focus atom property wm-name wm-class wm-protocols")
expect(state).to_equal("missing-wm-state")
```

</details>

#### returns ready when all required features are declared

- returns ready when all required features are declared
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ready when all required features are declared")
val state = x11_backend_gate("display screen window map-unmap configure surface damage clip expose present input focus atom property wm-name wm-class wm-protocols wm-state cursor clipboard text glyph blit fill")
expect(state).to_equal("ready")
```

</details>

### event coverage

#### requires a full window lifecycle and interaction stream

- requires a full window lifecycle and interaction stream
   - Expected: state equals `missing-unmap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a full window lifecycle and interaction stream")
val state = x11_backend_event_gate("create map configure expose focus input")
expect(state).to_equal("missing-unmap")
```

</details>

### pixel coverage

#### requires golden, damage, text, cursor, and present evidence

- requires golden, damage, text, cursor, and present evidence
   - Expected: state equals `missing-cursor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires golden, damage, text, cursor, and present evidence")
val state = x11_backend_pixel_gate("golden damage text")
expect(state).to_equal("missing-cursor")
```

</details>

### WM property coverage

#### requires X11 WM atoms and properties that Wine checks during window setup

- requires X11 WM atoms and properties that Wine checks during window setup
   - Expected: state equals `missing-_NET_WM_STATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires X11 WM atoms and properties that Wine checks during window setup")
val state = x11_backend_property_gate("WM_NAME WM_CLASS WM_PROTOCOLS")
expect(state).to_equal("missing-_NET_WM_STATE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/x11_backend_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X11-class backend readiness gate, feature coverage, event coverage, pixel coverage, WM property coverage.
- X11-class backend readiness gate
- feature coverage
- event coverage
- pixel coverage
- WM property coverage

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

- Canonical SPipe generation for source `74da2f696c701b9860108b9b553266ba75943e2ad6947af0fa57ad3cbbf8e238`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74da2f696c701b9860108b9b553266ba75943e2ad6947af0fa57ad3cbbf8e238`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74da2f696c701b9860108b9b553266ba75943e2ad6947af0fa57ad3cbbf8e238`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/x11_backend_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/x11_backend_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/x11_backend_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/x11_backend_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/x11_backend_gate_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists native WM features needed by a future Wine backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/x11_backend_gate_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing X11-class renderer feature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/x11_backend_gate_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ready when all required features are declared' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
