# Display Detect Specification

> Tests covering Display Detection, display_kind_name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Display Detect Specification

## Scenarios

### Display Detection

#### returns a DisplayInfo struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a DisplayInfo struct
   - Expected: name == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a DisplayInfo struct")
val info = detect_display()
# Just verify it returns without crashing
val name = display_kind_name(info.kind)
expect(name == "").to_equal(false)
```

</details>

#### has_any_display returns a boolean

- has_any_display returns a boolean
   - Expected: result == true or result == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_any_display returns a boolean")
val result = has_any_display()
# On any system this should return true or false
expect(result == true or result == false).to_equal(true)
```

</details>

#### can_show_gui returns a boolean

- can_show_gui returns a boolean
   - Expected: result == true or result == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can_show_gui returns a boolean")
val result = can_show_gui()
expect(result == true or result == false).to_equal(true)
```

</details>

### display_kind_name

#### names all display types

- names all display types
   - Expected: display_kind_name(DISPLAY_NONE) equals `none`
   - Expected: display_kind_name(DISPLAY_X11) equals `X11`
   - Expected: display_kind_name(DISPLAY_WAYLAND) equals `Wayland`
   - Expected: display_kind_name(DISPLAY_MACOS) equals `macOS`
   - Expected: display_kind_name(DISPLAY_XVFB) equals `Xvfb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names all display types")
expect(display_kind_name(DISPLAY_NONE)).to_equal("none")
expect(display_kind_name(DISPLAY_X11)).to_equal("X11")
expect(display_kind_name(DISPLAY_WAYLAND)).to_equal("Wayland")
expect(display_kind_name(DISPLAY_MACOS)).to_equal("macOS")
expect(display_kind_name(DISPLAY_XVFB)).to_equal("Xvfb")
```

</details>

#### handles unknown values

- handles unknown values
   - Expected: display_kind_name(99) equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown values")
expect(display_kind_name(99)).to_equal("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/display_detect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Display Detection, display_kind_name.
- Display Detection
- display_kind_name

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

- Canonical SPipe generation for source `bcd2659430784ddbe8cdbbe9a25145253d754cec6e083ab737c0ede38530f850`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bcd2659430784ddbe8cdbbe9a25145253d754cec6e083ab737c0ede38530f850`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bcd2659430784ddbe8cdbbe9a25145253d754cec6e083ab737c0ede38530f850`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/display_detect_spec.spl
mirror: doc/06_spec/unit/app/ui/display_detect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/display_detect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/display_detect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/display_detect_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a DisplayInfo struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/display_detect_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has_any_display returns a boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/display_detect_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can_show_gui returns a boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
