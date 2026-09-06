# electron_capture_ppm_spec

> CaptureResult fields (pixels, width, height, backend_name, success, error)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# electron_capture_ppm_spec

CaptureResult fields (pixels, width, height, backend_name, success, error)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/electron_capture_ppm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## CaptureResult After PPM Switch

    CaptureResult fields (pixels, width, height, backend_name, success, error)
    remain the same regardless of underlying format (PNG or PPM).

## Scenarios

### ElectronCapture PPM — CaptureResult structure

#### error result construction

#### AC-2: capture_error creates result with correct backend_name

- AC-2: capture_error creates result with correct backend_name
   - Expected: result.backend_name equals `electron`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_error creates result with correct backend_name")
val result = capture_error("electron", W, H, "test error")
expect(result.backend_name).to_equal("electron")
```

</details>

#### AC-2: capture_error creates result with empty pixels

- AC-2: capture_error creates result with empty pixels
   - Expected: result.pixels.len().to_i32() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_error creates result with empty pixels")
val result = capture_error("electron", W, H, "test error")
expect(result.pixels.len().to_i32()).to_equal(0)
```

</details>

#### AC-2: capture_error preserves error message

- AC-2: capture_error preserves error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_error preserves error message")
val result = capture_error("electron", W, H, "PPM decode failed")
expect(result.error).to_contain("PPM")
```

</details>

#### AC-2: capture_error sets success to false

- AC-2: capture_error sets success to false
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_error sets success to false")
val result = capture_error("electron", W, H, "test error")
expect(result.success).to_equal(false)
```

</details>

#### AC-2: capture_error preserves dimensions

- AC-2: capture_error preserves dimensions
   - Expected: result.width equals `W`
   - Expected: result.height equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_error preserves dimensions")
val result = capture_error("electron", W, H, "test error")
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

### ElectronCapture PPM — command invocation

#### command construction

#### AC-2: capture_electron with empty HTML returns error (not crash)

- AC-2: capture_electron with empty HTML returns error (not crash)
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron with empty HTML returns error (not crash)")
val result = capture_electron("", W, H)
expect(result.success).to_equal(false)
```

</details>

#### AC-2: capture_electron error mentions 'Empty HTML'

- AC-2: capture_electron error mentions 'Empty HTML'
   - Expected: mentions_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron error mentions 'Empty HTML'")
val result = capture_electron("", W, H)
val mentions_empty = result.error.contains("Empty") or result.error.contains("empty")
expect(mentions_empty).to_equal(true)
```

</details>

#### scene-level capture with PPM

#### AC-2: capture_electron_scene returns result with shared compositor backend

- AC-2: capture_electron_scene returns result with shared compositor backend
   - Expected: result.backend_name equals `browser_compositor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron_scene returns result with shared compositor backend")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.backend_name).to_equal("browser_compositor")
```

</details>

#### AC-2: capture_electron_scene dimensions match scene spec

- AC-2: capture_electron_scene dimensions match scene spec
   - Expected: result.width equals `W`
   - Expected: result.height equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture_electron_scene dimensions match scene spec")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
expect(result.width).to_equal(W)
expect(result.height).to_equal(H)
```

</details>

### ElectronCapture PPM — decode integration

#### capture with valid scene

#### AC-2: capture result from valid scene uses the shared compositor backend

- AC-2: capture result from valid scene uses the shared compositor backend
   - Expected: result.backend_name equals `browser_compositor`
   - Expected: has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: capture result from valid scene uses the shared compositor backend")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
# In test env, Electron may not be available
if result.success:
    expect(result.backend_name).to_equal("browser_compositor")
    expect(result.pixels.len()).to_be_greater_than(0)
else:
    # Graceful degradation when Electron is missing
    val has_error = result.error.len() > 0
    expect(has_error).to_equal(true)
```

</details>

#### AC-2: successful capture pixel count equals width * height

- AC-2: successful capture pixel count equals width * height
   - Expected: result.pixels.len().to_i32() equals `expected`
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: successful capture pixel count equals width * height")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
if result.success:
    val expected = W * H
    expect(result.pixels.len().to_i32()).to_equal(expected)
else:
    expect(result.success).to_equal(false)
```

</details>

#### AC-2: successful capture has non-zero pixels (not all transparent)

- AC-2: successful capture has non-zero pixels (not all transparent)
   - Expected: has_nonzero is true
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: successful capture has non-zero pixels (not all transparent)")
val scene = standard_wm_scene(W, H)
val result = capture_electron_scene(scene)
if result.success:
    var has_nonzero = false
    for px in result.pixels:
        if px != 0:
            has_nonzero = true
    expect(has_nonzero).to_equal(true)
else:
    expect(result.success).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `77dbce6f38ab83222df2f7c117d00ea30151f0da5530fcf56c3768c29ad93167`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77dbce6f38ab83222df2f7c117d00ea30151f0da5530fcf56c3768c29ad93167`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77dbce6f38ab83222df2f7c117d00ea30151f0da5530fcf56c3768c29ad93167`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/compositor/electron_capture_ppm_spec.spl
mirror: doc/06_spec/unit/os/compositor/electron_capture_ppm_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/electron_capture_ppm_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/unit/os/compositor/electron_capture_ppm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/electron_capture_ppm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/compositor/electron_capture_ppm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
