# qemu_capture_ppm_spec

capture_qemu_inprocess renders the scene on BrowserCompositorBackend

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/qemu_capture_ppm_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## In-Process Capture

    capture_qemu_inprocess renders the scene on BrowserCompositorBackend
    and returns raw ARGB [u32] pixels directly. No PPM decode needed
    for this path — pixels come straight from the software renderer.

## Scenarios

### QemuCapture PPM — in-process capture

#### valid scene rendering

#### AC-3: in-process capture returns success for standard scene

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

#### AC-3: in-process capture pixel buffer is non-empty

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

#### AC-3: in-process capture pixel count equals width * height

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
val expected = W * H
expect(result.pixels.len().to_i32()).to_equal(expected)
```

</details>

#### AC-3: in-process capture has correct dimensions

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

#### AC-3: in-process capture backend_name is the shared compositor backend

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

#### pixel content validity

#### AC-3: rendered pixels contain non-zero values (scene has content)

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
var has_nonzero = false
for px in result.pixels:
    if px != 0:
        has_nonzero = true
expect(has_nonzero).to_equal(true)
```

</details>

#### AC-3: rendered pixels have valid alpha channel (0xFF for opaque)

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val result = capture_qemu_inprocess(scene)
if result.pixels.len() > 0:
    # Check first pixel has alpha
    val alpha = (result.pixels[0] >> 24) & 0xFF
    expect(alpha).to_be_greater_than(0)
else:
    expect(result.pixels.len()).to_be_greater_than(0)
```

</details>

### QemuCapture PPM — VM capture format

#### invalid socket (graceful error)

#### AC-3: VM capture with nonexistent socket returns failure

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_ppm.ppm")
expect(result.success).to_equal(false)
```

</details>

#### AC-3: VM capture failure has descriptive error message

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_ppm.ppm")
val has_msg = result.error.len() > 0
expect(has_msg).to_equal(true)
```

</details>

#### AC-3: VM capture failure returns qemu_vm backend name

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_ppm.ppm")
expect(result.backend_name).to_equal("qemu_vm")
```

</details>

#### AC-3: VM capture failure returns empty pixel buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test_ppm.ppm")
expect(result.pixels.len().to_i32()).to_equal(0)
```

</details>

### QemuCapture PPM — result consistency

#### field presence on both paths

#### AC-3: both paths produce CaptureResult with width field

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val inprocess = capture_qemu_inprocess(scene)
val vm = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test.ppm")
val both_have_width = inprocess.width >= 0 and vm.width >= 0
expect(both_have_width).to_equal(true)
```

</details>

#### AC-3: both paths produce CaptureResult with height field

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val inprocess = capture_qemu_inprocess(scene)
val vm = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test.ppm")
val both_have_height = inprocess.height >= 0 and vm.height >= 0
expect(both_have_height).to_equal(true)
```

</details>

#### AC-3: both paths produce CaptureResult with success field

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val inprocess = capture_qemu_inprocess(scene)
val vm = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test.ppm")
# inprocess should succeed, vm should fail (no socket)
expect(inprocess.success).to_equal(true)
expect(vm.success).to_equal(false)
```

</details>

#### AC-3: in-process success has empty error; VM failure has non-empty error

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val inprocess = capture_qemu_inprocess(scene)
val vm = capture_qemu_vm("/nonexistent/qmp.sock", "/tmp/test.ppm")
val inprocess_no_error = inprocess.error.len() == 0
val vm_has_error = vm.error.len() > 0
expect(inprocess_no_error).to_equal(true)
expect(vm_has_error).to_equal(true)
```

</details>

### QemuCapture PPM — screendump decode

#### valid P6 data

#### AC-3: decodes QMP screendump PPM bytes into qemu_vm CaptureResult

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [80u8, 54u8, 10u8, 50u8, 32u8, 49u8, 10u8, 50u8, 53u8, 53u8, 10u8, 255u8, 0u8, 0u8, 0u8, 255u8, 0u8]
val result = decode_qemu_screendump_ppm(data)
expect(result.success).to_equal(true)
expect(result.backend_name).to_equal("qemu_vm")
expect(result.width).to_equal(2)
expect(result.height).to_equal(1)
expect(result.pixels.len()).to_equal(2)
expect(result.pixels[0]).to_equal(0xFFFF0000u32)
expect(result.pixels[1]).to_equal(0xFF00FF00u32)
```

</details>

#### invalid PPM data

#### AC-3: reports decode failure without crashing

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_qemu_screendump_ppm([80u8, 51u8, 10u8])
expect(result.success).to_equal(false)
expect(result.backend_name).to_equal("qemu_vm")
expect(result.error).to_contain("PPM")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

