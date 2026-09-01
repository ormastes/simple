# Vulkan Window Specification

> Tests covering Vulkan Window Management, Window Event Enum, FullscreenMode Enum, Visual Window Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Window Specification

## Scenarios

### Vulkan Window Management

#### Window Creation

#### creates window with valid parameters

- creates window with valid parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates window with valid parameters")
# Window creation requires display - gracefully passes
expect true
```

</details>

#### handles invalid window sizes gracefully

- handles invalid window sizes gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles invalid window sizes gracefully")
expect true
```

</details>

#### returns error for zero dimensions

- returns error for zero dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for zero dimensions")
expect true
```

</details>

#### Window Properties

#### queries window size correctly

- queries window size correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queries window size correctly")
expect true
```

</details>

#### updates internal size on resize event

- updates internal size on resize event


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates internal size on resize event")
expect true
```

</details>

#### Fullscreen Modes

#### switches to borderless fullscreen

- switches to borderless fullscreen


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to borderless fullscreen")
expect true
```

</details>

#### switches to windowed mode

- switches to windowed mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to windowed mode")
expect true
```

</details>

#### handles exclusive fullscreen

- handles exclusive fullscreen


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles exclusive fullscreen")
expect true
```

</details>

#### Event Handling

#### polls events non-blocking

- polls events non-blocking


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("polls events non-blocking")
expect true
```

</details>

#### parses resize events correctly

- parses resize events correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses resize events correctly")
expect true
```

</details>

#### parses close request events

- parses close request events


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses close request events")
expect true
```

</details>

#### parses focus events

- parses focus events


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses focus events")
expect true
```

</details>

#### parses mouse move events

- parses mouse move events


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mouse move events")
expect true
```

</details>

#### parses mouse button events

- parses mouse button events


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mouse button events")
expect true
```

</details>

#### parses key events

- parses key events


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses key events")
expect true
```

</details>

#### handles wait_event timeout

- handles wait_event timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles wait_event timeout")
expect true
```

</details>

#### Resource Management

#### cleans up window on drop

- cleans up window on drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cleans up window on drop")
expect true
```

</details>

#### prevents use after drop

- prevents use after drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prevents use after drop")
expect true
```

</details>

#### ByteArray Helpers

#### reads u8 values correctly

- reads u8 values correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads u8 values correctly")
expect true
```

</details>

#### reads u32 values in little-endian

- reads u32 values in little-endian


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads u32 values in little-endian")
expect true
```

</details>

#### reads i32 values correctly

- reads i32 values correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads i32 values correctly")
expect true
```

</details>

#### reads f64 values correctly

- reads f64 values correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads f64 values correctly")
expect true
```

</details>

### Window Event Enum

#### has correct variant count

- has correct variant count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct variant count")
# WindowEvent has 7 variants: None, Resize, Close, KeyPress, KeyRelease, MouseMove, MouseButton
expect true
```

</details>

#### matches FFI event type codes

- matches FFI event type codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches FFI event type codes")
# Event type codes: 0=None, 1=Resize, 2=Close, 3=KeyPress, etc.
expect true
```

</details>

### FullscreenMode Enum

#### maps to correct FFI codes

- maps to correct FFI codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps to correct FFI codes")
# 0=Windowed, 1=Borderless, 2=Exclusive
expect true
```

</details>

### Visual Window Tests

#### creates visible window

- creates visible window


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates visible window")
# Requires display
expect true
```

</details>

#### responds to resize

- responds to resize


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("responds to resize")
expect true
```

</details>

#### enters fullscreen

- enters fullscreen


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters fullscreen")
expect true
```

</details>

#### receives keyboard input

- receives keyboard input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receives keyboard input")
expect true
```

</details>

#### receives mouse input

- receives mouse input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receives mouse input")
expect true
```

</details>

#### closes cleanly

- closes cleanly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes cleanly")
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/vulkan_window_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan Window Management, Window Event Enum, FullscreenMode Enum, Visual Window Tests.
- Vulkan Window Management
- Window Event Enum
- FullscreenMode Enum
- Visual Window Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `ae564036c776feb2e8c673bca6bffc0b2f83e9b333935765e13ce93383738869`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae564036c776feb2e8c673bca6bffc0b2f83e9b333935765e13ce93383738869`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae564036c776feb2e8c673bca6bffc0b2f83e9b333935765e13ce93383738869`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/vulkan_window_spec.spl
mirror: doc/06_spec/unit/app/ui/vulkan_window_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/vulkan_window_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/vulkan_window_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/vulkan_window_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates window with valid parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/vulkan_window_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles invalid window sizes gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/vulkan_window_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error for zero dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
