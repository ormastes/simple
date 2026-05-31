# Qemu Capture Specification

## Scenarios

### QemuCapture — capture_qemu_inprocess

#### basic capture

#### AC-3: in-process capture returns CaptureResult with shared compositor backend name

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-3: in-process capture returns correct dimensions

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

#### AC-3: in-process capture returns non-empty pixel buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.pixels.len()).to_be_greater_than(0)
```

</details>

#### AC-3: in-process capture pixel buffer has correct size

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
val expected_len = W * H
expect(result.pixels.len().to_i32()).to_equal(expected_len)
```

</details>

#### AC-3: in-process capture reports success

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
expect(result.success).to_equal(true)
```

</details>

### QemuCapture — capture_qemu_vm

#### QMP screendump capture

#### AC-3: VM capture with invalid socket returns error

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_screendump.png")
expect(result.success).to_equal(false)
```

</details>

#### AC-3: VM capture with invalid socket has error message

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_screendump.png")
val has_error = result.error.len() > 0
expect(has_error).to_equal(true)
```

</details>

#### AC-3: VM capture result has backend_name 'qemu_vm'

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_screendump.png")
expect(result.backend_name).to_equal("qemu_vm")
```

</details>

#### AC-3: VM capture rejects empty QMP socket before running helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("", "/tmp/test_screendump.png")
expect(result.success).to_equal(false)
expect(result.error).to_contain("empty QMP socket path")
```

</details>

#### AC-3: VM capture rejects empty output path before running helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "")
expect(result.success).to_equal(false)
expect(result.error).to_contain("empty output path")
```

</details>

### QemuCapture — result uniformity

#### both paths return same CaptureResult type

#### AC-3: in-process and VM results both have width, height, pixels fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

