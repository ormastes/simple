# Background Gradient Over Color Specification

> Tests covering background shorthand: typed image layer over a base colour.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Background Gradient Over Color Specification

## Scenarios

### background shorthand: typed image layer over a base colour

#### types a gradient-over-colour panel background instead of keeping it raw

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- types a gradient-over-colour panel background instead of keeping it raw
   - Expected: _style_value(probe, "background-layers-raw") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("types a gradient-over-colour panel background instead of keeping it raw")
val probe = _probe_command(_panel_background)
expect(_style_value(probe, "background-layers-raw")).to_equal("")
expect(_style_value(probe, "background-color")).to_equal(
    "{(184u32 << 24) | (20u32 << 16) | (22u32 << 8) | 32u32}")
expect(
    _style_value(probe, "background-image")
).to_contain("linear-gradient(")
```

</details>

#### still refuses two stacked gradients (no base colour layer)

- still refuses two stacked gradients (no base colour layer)
   - Expected: _style_value(probe, "background-image") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still refuses two stacked gradients (no base colour layer)")
val probe = _probe_command(
    "background: linear-gradient(180deg, rgba(255,255,255,0.09), " +
    "rgba(255,255,255,0.02)), linear-gradient(90deg, red, blue);")
expect(_style_value(probe, "background-layers-raw")).to_not_equal("")
expect(_style_value(probe, "background-image")).to_equal("none")
```

</details>

#### still refuses an untyped image function over a colour

- still refuses an untyped image function over a colour
   - Expected: _style_value(probe, "background-image") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still refuses an untyped image function over a colour")
val probe = _probe_command(
    "background: conic-gradient(red, blue), rgba(20,22,32,0.72);")
expect(_style_value(probe, "background-layers-raw")).to_not_equal("")
expect(_style_value(probe, "background-image")).to_equal("none")
```

</details>

#### still refuses an unresolved var() as the base layer

- still refuses an unresolved var() as the base layer
   - Expected: _style_value(probe, "background-image") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still refuses an unresolved var() as the base layer")
val probe = _probe_command(
    "background: linear-gradient(180deg, rgba(255,255,255,0.09), " +
    "rgba(255,255,255,0.02)), var(--nope);")
expect(_style_value(probe, "background-layers-raw")).to_not_equal("")
expect(_style_value(probe, "background-image")).to_equal("none")
```

</details>

#### still refuses three layers

- still refuses three layers
   - Expected: _style_value(probe, "background-image") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still refuses three layers")
val probe = _probe_command(
    "background: linear-gradient(180deg, red, blue), " +
    "linear-gradient(90deg, red, blue), rgba(20,22,32,0.72);")
expect(_style_value(probe, "background-layers-raw")).to_not_equal("")
expect(_style_value(probe, "background-image")).to_equal("none")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering background shorthand: typed image layer over a base colour.
- background shorthand: typed image layer over a base colour

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

- Canonical SPipe generation for source `b78f1a4502d2708f76b14f1dfc5a57998587869ab6df38c7097cd5c33ffbbc50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b78f1a4502d2708f76b14f1dfc5a57998587869ab6df38c7097cd5c33ffbbc50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b78f1a4502d2708f76b14f1dfc5a57998587869ab6df38c7097cd5c33ffbbc50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'types a gradient-over-colour panel background instead of keeping it raw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still refuses two stacked gradients (no base colour layer)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/background_gradient_over_color_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still refuses an untyped image function over a colour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
