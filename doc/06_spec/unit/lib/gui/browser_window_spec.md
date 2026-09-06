# Browser Window Specification

> Tests covering BrowserWindow.new, WindowStyle.default, BrowserWindow visibility, BrowserWindow mutations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Window Specification

## Scenarios

### BrowserWindow.new

#### sets id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sets id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets id")
val w = _make_window()
expect w.id to_equal 99
```

</details>

#### sets title

- sets title


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets title")
val w = _make_window()
expect w.title to_equal "Test Window"
```

</details>

#### sets bounds

- sets bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets bounds")
val w = _make_window()
expect w.bounds.right to_equal 1280.0
```

</details>

### WindowStyle.default

#### has frame=true

- has frame=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has frame=true")
val s = WindowStyle.default()
expect s.frame to_equal true
```

</details>

#### has transparent=false

- has transparent=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has transparent=false")
val s = WindowStyle.default()
expect s.transparent to_equal false
```

</details>

### BrowserWindow visibility

#### show sets is_visible=true

- show sets is_visible=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("show sets is_visible=true")
var w = _make_window()
w.show()
expect w.is_visible to_equal true
```

</details>

#### hide sets is_visible=false

- hide sets is_visible=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hide sets is_visible=false")
var w = _make_window()
w.show()
w.hide()
expect w.is_visible to_equal false
```

</details>

### BrowserWindow mutations

#### set_title updates

- set_title updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_title updates")
var w = _make_window()
w.set_title("Updated")
expect w.title to_equal "Updated"
```

</details>

#### set_bounds updates

- set_bounds updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_bounds updates")
var w = _make_window()
val new_bounds = SkRect(left: 0.0, top: 0.0, right: 640.0, bottom: 480.0)
w.set_bounds(new_bounds)
expect w.bounds.right to_equal 640.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gui/browser_window_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserWindow.new, WindowStyle.default, BrowserWindow visibility, BrowserWindow mutations.
- BrowserWindow.new
- WindowStyle.default
- BrowserWindow visibility
- BrowserWindow mutations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `624cc5228ce0b9f6899b0fae431d549329310cf2cab9f97bc3301d825e7873c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `624cc5228ce0b9f6899b0fae431d549329310cf2cab9f97bc3301d825e7873c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `624cc5228ce0b9f6899b0fae431d549329310cf2cab9f97bc3301d825e7873c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gui/browser_window_spec.spl
mirror: doc/06_spec/unit/lib/gui/browser_window_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gui/browser_window_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gui/browser_window_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gui/browser_window_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gui/browser_window_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gui/browser_window_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
