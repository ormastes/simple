# metal_strict_spec

> Purpose: This spec proves Metal strict smoke tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_strict_spec

Purpose: This spec proves Metal strict smoke tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/metal_strict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Metal strict smoke tests.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Metal strict smoke tests

#### probe_metal() platform diagnostics

#### always returns a BackendProbeResult (never panics)

- always returns a BackendProbeResult (never panics)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-METALSTRICT-001
step("always returns a BackendProbeResult (never panics)")
val result = probe_metal()
# Just confirm we got a result — any status is valid
val status_text = result.diagnostic_text()
expect(status_text.len()).to_be_greater_than(0)
```

</details>

#### on Linux: status is Unavailable

- on Linux: status is Unavailable
- on Linux: status is Unavailable
   - Expected: result.status equals `BackendStatus.Unavailable`
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: status is Unavailable")
step("on Linux: status is Unavailable")
if os_is_linux():
    val result = probe_metal()
    expect(result.status).to_equal(BackendStatus.Unavailable)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: reason contains 'macOS'

- on Linux: reason contains 'macOS'
- on Linux: reason contains 'macOS'
   - Expected: result.fallback_reason contains `macOS`
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: reason contains 'macOS'")
step("on Linux: reason contains 'macOS'")
if os_is_linux():
    val result = probe_metal()
    expect(result.fallback_reason.contains("macOS")).to_equal(true)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: feature gate is 'macos'

- on Linux: feature gate is 'macos'
- on Linux: feature gate is 'macos'
   - Expected: result.feature_gate equals `macos`
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: feature gate is 'macos'")
step("on Linux: feature gate is 'macos'")
if os_is_linux():
    val result = probe_metal()
    expect(result.feature_gate).to_equal("macos")
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: requested_name is 'metal'

- on Linux: requested_name is 'metal'
- on Linux: requested_name is 'metal'
   - Expected: result.requested_name equals `metal`
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: requested_name is 'metal'")
step("on Linux: requested_name is 'metal'")
if os_is_linux():
    val result = probe_metal()
    expect(result.requested_name).to_equal("metal")
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on macOS: probe_metal returns initialized or failed (not unavailable)

- on macOS: probe_metal returns initialized or failed (not unavailable)
- on macOS: probe_metal returns initialized or failed (not unavailable)
   - Expected: not_unavailable is true
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on macOS: probe_metal returns initialized or failed (not unavailable)")
step("on macOS: probe_metal returns initialized or failed (not unavailable)")
if os_is_macos():
    val result = probe_metal()
    val not_unavailable = result.status != BackendStatus.Unavailable
    expect(not_unavailable).to_equal(true)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### Engine2D.create_with_backend_strict metal

#### always returns a Result (never panics)

- always returns a Result (never panics)
- always returns a Result (never panics)
   - Expected: engine.width() equals `16`
   - Expected: diag.requested_name equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("always returns a Result (never panics)")
step("always returns a Result (never panics)")
val result = Engine2D.create_with_backend_strict(16, 16, "metal")
if result.is_ok():
    var engine = result.unwrap()
    expect(engine.width()).to_equal(16)
    engine.shutdown()
else:
    val diag = result.unwrap_err()
    expect(diag.requested_name).to_equal("metal")
```

</details>

#### on Linux: returns Err

- on Linux: returns Err
- on Linux: returns Err
   - Expected: result.is_ok() is false
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: returns Err")
step("on Linux: returns Err")
if os_is_linux():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    expect(result.is_ok()).to_equal(false)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: Err carries BackendProbeResult with Unavailable status

- on Linux: Err carries BackendProbeResult with Unavailable status
- on Linux: Err carries BackendProbeResult with Unavailable status
   - Expected: diag.status equals `BackendStatus.Unavailable`
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: Err carries BackendProbeResult with Unavailable status")
step("on Linux: Err carries BackendProbeResult with Unavailable status")
if os_is_linux():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if not result.is_ok():
        val diag = result.unwrap_err()
        expect(diag.status).to_equal(BackendStatus.Unavailable)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on Linux: Err reason contains 'macOS'

- on Linux: Err reason contains 'macOS'
- on Linux: Err reason contains 'macOS'
   - Expected: diag.fallback_reason contains `macOS`
   - Expected: os_is_linux() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on Linux: Err reason contains 'macOS'")
step("on Linux: Err reason contains 'macOS'")
if os_is_linux():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if not result.is_ok():
        val diag = result.unwrap_err()
        expect(diag.fallback_reason.contains("macOS")).to_equal(true)
else:
    expect(os_is_linux()).to_equal(false)
```

</details>

#### on macOS: returns Ok or typed failed diagnostic

- on macOS: returns Ok or typed failed diagnostic
- on macOS: returns Ok or typed failed diagnostic
   - Expected: engine.width() equals `16`
   - Expected: engine.height() equals `16`
   - Expected: diag.status equals `BackendStatus.Failed`
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on macOS: returns Ok or typed failed diagnostic")
step("on macOS: returns Ok or typed failed diagnostic")
if os_is_macos():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if result.is_ok():
        var engine = result.unwrap()
        expect(engine.width()).to_equal(16)
        expect(engine.height()).to_equal(16)
        engine.shutdown()
    else:
        val diag = result.unwrap_err()
        expect(diag.status).to_equal(BackendStatus.Failed)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### macOS Metal rendering smoke (draw + readback)

#### on macOS: clear sets all pixels to given color

- on macOS: clear sets all pixels to given color
- on macOS: clear sets all pixels to given color
   - Expected: all_red is true
   - Expected: diag.status equals `BackendStatus.Failed`
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on macOS: clear sets all pixels to given color")
step("on macOS: clear sets all pixels to given color")
if os_is_macos():
    val result = Engine2D.create_with_backend_strict(4, 4, "metal")
    if result.is_ok():
        var engine = result.unwrap()
        val red = rgb(255, 0, 0)
        engine.clear(red)
        engine.present()
        val pixels = engine.read_pixels()
        var all_red = true
        var i = 0
        while i < 16:
            if pixels[i] != red:
                all_red = false
            i = i + 1
        engine.shutdown()
        expect(all_red).to_equal(true)
    else:
        val diag = result.unwrap_err()
        expect(diag.status).to_equal(BackendStatus.Failed)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### on macOS: draw_rect_filled produces non-zero pixels in region

- on macOS: draw_rect_filled produces non-zero pixels in region
- on macOS: draw_rect_filled produces non-zero pixels in region
   - Expected: top_left equals `blue`
   - Expected: diag.status equals `BackendStatus.Failed`
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on macOS: draw_rect_filled produces non-zero pixels in region")
step("on macOS: draw_rect_filled produces non-zero pixels in region")
if os_is_macos():
    val result = Engine2D.create_with_backend_strict(16, 16, "metal")
    if result.is_ok():
        var engine = result.unwrap()
        engine.clear(0u32)
        val blue = rgb(0, 0, 255)
        engine.draw_rect_filled(0, 0, 8, 8, blue)
        engine.present()
        val pixels = engine.read_pixels()
        # Top-left pixel (0,0) should be blue
        val top_left = pixels[0]
        engine.shutdown()
        expect(top_left).to_equal(blue)
    else:
        val diag = result.unwrap_err()
        expect(diag.status).to_equal(BackendStatus.Failed)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

#### on macOS: CPU backend and Metal produce same clear result

- on macOS: CPU backend and Metal produce same clear result
- on macOS: CPU backend and Metal produce same clear result
   - Expected: parity is true
   - Expected: diag.status equals `BackendStatus.Failed`
   - Expected: os_is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("on macOS: CPU backend and Metal produce same clear result")
step("on macOS: CPU backend and Metal produce same clear result")
if os_is_macos():
    val metal_result = Engine2D.create_with_backend_strict(4, 4, "metal")
    var cpu_engine = Engine2D.create_with_backend(4, 4, "cpu")
    val green = rgb(0, 255, 0)
    cpu_engine.clear(green)
    cpu_engine.present()
    val cpu_pixels = cpu_engine.read_pixels()
    cpu_engine.shutdown()

    if metal_result.is_ok():
        var metal_engine = metal_result.unwrap()
        metal_engine.clear(green)
        metal_engine.present()
        val metal_pixels = metal_engine.read_pixels()
        metal_engine.shutdown()

        var parity = true
        var i = 0
        while i < 16:
            if metal_pixels[i] != cpu_pixels[i]:
                parity = false
            i = i + 1
        expect(parity).to_equal(true)
    else:
        val diag = metal_result.unwrap_err()
        expect(diag.status).to_equal(BackendStatus.Failed)
else:
    expect(os_is_macos()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-METALSTRICT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9077aac135dd03c267975f505e3e185b498f05883342c5d3dc2fa0ba0b7d52af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9077aac135dd03c267975f505e3e185b498f05883342c5d3dc2fa0ba0b7d52af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9077aac135dd03c267975f505e3e185b498f05883342c5d3dc2fa0ba0b7d52af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/metal_strict_spec.spl
mirror: doc/06_spec/integration/rendering/metal_strict_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/metal_strict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/metal_strict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/metal_strict_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/metal_strict_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'always returns a BackendProbeResult (never panics)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/metal_strict_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'on Linux: status is Unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/metal_strict_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'on Linux: reason contains 'macOS'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
