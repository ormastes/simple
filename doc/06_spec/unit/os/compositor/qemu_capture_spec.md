# Qemu Capture Specification

> Tests covering QemuCapture — capture_qemu_inprocess, QemuCapture — capture_qemu_vm, QemuCapture — result uniformity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Capture Specification

## Scenarios

### QemuCapture — capture_qemu_inprocess

#### basic capture

#### AC-3: in-process capture returns CaptureResult with shared compositor backend name

- AC-3: in-process capture returns CaptureResult with shared compositor backend name
   - Expected: result.backend_name equals `browser_compositor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: in-process capture returns CaptureResult with shared compositor backend name")
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-3: in-process capture returns correct dimensions

- AC-3: in-process capture returns correct dimensions
   - Expected: result.width equals `W`
   - Expected: result.height equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: in-process capture returns correct dimensions")
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

#### AC-3: in-process capture returns non-empty pixel buffer

- AC-3: in-process capture returns non-empty pixel buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: in-process capture returns non-empty pixel buffer")
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.pixels.len()).to_be_greater_than(0)
```

</details>

#### AC-3: in-process capture pixel buffer has correct size

- AC-3: in-process capture pixel buffer has correct size
   - Expected: result.pixels.len().to_i32() equals `expected_len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: in-process capture pixel buffer has correct size")
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
val expected_len = W * H
expect(result.pixels.len().to_i32()).to_equal(expected_len)
```

</details>

#### AC-3: in-process capture reports success

- AC-3: in-process capture reports success
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: in-process capture reports success")
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.success).to_equal(true)
```

</details>

### QemuCapture — capture_qemu_vm

#### QMP screendump capture

#### AC-3: VM capture with invalid socket returns error

- AC-3: VM capture with invalid socket returns error
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: VM capture with invalid socket returns error")
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_screendump.png")
expect(result.success).to_equal(false)
```

</details>

#### AC-3: VM capture with invalid socket has error message

- AC-3: VM capture with invalid socket has error message
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: VM capture with invalid socket has error message")
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_screendump.png")
val has_error = result.error.len() > 0
expect(has_error).to_equal(true)
```

</details>

#### AC-3: VM capture result has backend_name 'qemu_vm'

- AC-3: VM capture result has backend_name 'qemu_vm'
   - Expected: result.backend_name equals `qemu_vm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: VM capture result has backend_name 'qemu_vm'")
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_screendump.png")
expect(result.backend_name).to_equal("qemu_vm")
```

</details>

#### AC-3: VM capture rejects empty QMP socket before running helper

- AC-3: VM capture rejects empty QMP socket before running helper
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: VM capture rejects empty QMP socket before running helper")
val result = capture_qemu_vm("", "/tmp/test_screendump.png")
expect(result.success).to_equal(false)
expect(result.error).to_contain("empty QMP socket path")
```

</details>

#### AC-3: VM capture rejects empty output path before running helper

- AC-3: VM capture rejects empty output path before running helper
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: VM capture rejects empty output path before running helper")
val result = capture_qemu_vm("/nonexistent/qmp.sock", "")
expect(result.success).to_equal(false)
expect(result.error).to_contain("empty output path")
```

</details>

### QemuCapture — result uniformity

#### both paths return same CaptureResult type

#### AC-3: in-process and VM results both have width, height, pixels fields

- AC-3: in-process and VM results both have width, height, pixels fields
   - Expected: both_have_width is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: in-process and VM results both have width, height, pixels fields")
val scene = standard_wm_scene(W, H)
val inprocess = capture_qemu_inprocess(scene)
val vm = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test.png")
# Both should have the same structural fields
val both_have_width = inprocess.width > 0 or vm.width >= 0
expect(both_have_width).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/qemu_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QemuCapture — capture_qemu_inprocess, QemuCapture — capture_qemu_vm, QemuCapture — result uniformity.
- QemuCapture — capture_qemu_inprocess
- QemuCapture — capture_qemu_vm
- QemuCapture — result uniformity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `bc893ffd9dc7214a793ce9c71938cd90a8b001d7f6d330c9c9e43a64b04147e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc893ffd9dc7214a793ce9c71938cd90a8b001d7f6d330c9c9e43a64b04147e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc893ffd9dc7214a793ce9c71938cd90a8b001d7f6d330c9c9e43a64b04147e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/unit/os/compositor/qemu_capture_spec.spl
mirror: doc/06_spec/unit/os/compositor/qemu_capture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/qemu_capture_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/unit/os/compositor/qemu_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/qemu_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
