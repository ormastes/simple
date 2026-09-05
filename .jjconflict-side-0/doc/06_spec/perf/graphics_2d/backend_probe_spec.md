# Backend Probe Specification

> Tests covering Engine2D strict backend probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Probe Specification

## Scenarios

### Engine2D strict backend probe

#### portable CPU baseline

#### initializes, renders, and reads back without fallback

- create the strict cpu backend, render, and read back provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-GPU-BACKEND-PROBE
step("create the strict cpu backend, render, and read back provenance")
assert_strict_backend("cpu", "none")
```

</details>

#### native GPU backends

<details>
<summary>Advanced: executes CUDA when initialized or reports structured unavailability</summary>

#### executes CUDA when initialized or reports structured unavailability _(slow)_

- probe and strictly create the cuda backend, assert structured outcome


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-GPU-BACKEND-PROBE
step("probe and strictly create the cuda backend, assert structured outcome")
assert_strict_backend("cuda", "ptx")
```

</details>


</details>

<details>
<summary>Advanced: executes Vulkan SPIR-V when initialized or reports structured unavailability</summary>

#### executes Vulkan SPIR-V when initialized or reports structured unavailability _(slow)_

- probe and strictly create the vulkan backend, assert structured outcome


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-GPU-BACKEND-PROBE
step("probe and strictly create the vulkan backend, assert structured outcome")
assert_strict_backend("vulkan", "spirv")
```

</details>


</details>

<details>
<summary>Advanced: keeps a multi-primitive Vulkan frame exact and device-backed</summary>

#### keeps a multi-primitive Vulkan frame exact and device-backed _(slow)_

- render a multi-primitive scene on vulkan and compare bit-exact against cpu
   - Expected: probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed is true
   - Expected: actual.source == "cpu_mirror" is false
   - Expected: actual.pixels.len() equals `expected.len()`
   - Expected: actual.pixels[i] equals `expected[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-GPU-BACKEND-PROBE
step("render a multi-primitive scene on vulkan and compare bit-exact against cpu")
val probe = Engine2D.probe_backend(32, 24, "vulkan")
val probe_ready = probe.status == BackendStatus.Initialized
if not probe_ready:
    expect(probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed).to_equal(true)
# The create is independent of the probe, so it is attempted
# regardless and every assertion below reads the create/readback.
val strict = Engine2D.create_with_backend_strict(32, 24, "vulkan")
val created = strict.is_ok()
if probe_ready != created:
    print "[toctou] vulkan-multi-primitive: probe predicted ready={probe_ready} but the independent create returned ok={created} — the prediction did not survive the gap; asserting on the CREATE, not the probe"
if created:
    var vulkan = strict.unwrap()
    var cpu = Engine2D.create_with_backend(32, 24, "cpu")
    paint_vulkan_probe_scene(cpu)
    paint_vulkan_probe_scene(vulkan)
    val expected = cpu.read_pixels()
    val actual = vulkan.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-multi-primitive", actual.source,
        actual.backend_handle, actual.device_identity, actual.pixel_count,
        (32 * 24).to_i64())
    # Same owned-create claim as above: a strict vulkan create that
    # succeeded may never silently report cpu_mirror.
    expect(actual.source == "cpu_mirror").to_equal(false)
    _report_outcome("vulkan-multi-primitive", actual.source, actual.backend_handle,
        actual.device_identity, actual.pixel_count, (32 * 24).to_i64())
    # Bit-exact parity against the CPU oracle holds for whichever
    # backend actually served the frame — strictly more coverage than
    # the old GPU-only branch. Skipped only when NO frame was produced,
    # since those sources carry an empty pixel array.
    if _source_is_no_frame(actual.source):
        print "[probe-gpu] vulkan-multi-primitive: FRAME ASSERTIONS SKIPPED — no frame was produced (source={actual.source}, {actual.pixel_count} pixels); this example proves NOTHING about rendering correctness"
    else:
        expect(actual.pixels.len()).to_equal(expected.len())
        var i = 0
        while i < expected.len():
            expect(actual.pixels[i]).to_equal(expected[i])
            i = i + 1
    cpu.shutdown()
    vulkan.shutdown()
else:
    val failure = strict.unwrap_err()
    _assert_strict_failure_is_structured("vulkan-multi-primitive", failure.selected_name)
```

</details>


</details>

<details>
<summary>Advanced: executes Metal MSL when initialized or reports structured unavailability</summary>

#### executes Metal MSL when initialized or reports structured unavailability _(slow)_

- probe and strictly create the metal backend, assert structured outcome


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-GPU-BACKEND-PROBE
step("probe and strictly create the metal backend, assert structured outcome")
assert_strict_backend("metal", "msl")
```

</details>


</details>

#### reports the macOS Metal gate without emulation on non-macOS hosts

- probe metal on a non-macOS host and assert the platform feature gate
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.feature_gate equals `macos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-GPU-BACKEND-PROBE
step("probe metal on a non-macOS host and assert the platform feature gate")
if not is_macos():
    val probe = Engine2D.probe_backend(16, 16, "metal")
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    expect(probe.feature_gate).to_equal("macos")
print "[probe-gpu] RUN VERDICT: this run's GPU evidence is exactly the set of '[probe-gpu] <backend>: GPU-PROVEN' lines above."
print "[probe-gpu] RUN VERDICT: every '[probe-gpu] <backend>: GPU BRANCH SKIPPED' line marks an example that proves NOTHING about the GPU path."
print "[probe-gpu] RUN VERDICT: a PASS with no GPU-PROVEN line does NOT attest any GPU backend — read it as 'device unavailable', not as 'GPU works'."
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/graphics_2d/backend_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D strict backend probe.
- Engine2D strict backend probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-GPU-BACKEND-PROBE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce61b45f6b8c6816e2ffb46a136be47a8000fc5f8f321c21c4904f29f881f487`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce61b45f6b8c6816e2ffb46a136be47a8000fc5f8f321c21c4904f29f881f487`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce61b45f6b8c6816e2ffb46a136be47a8000fc5f8f321c21c4904f29f881f487`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/perf/graphics_2d/backend_probe_spec.spl
mirror: doc/06_spec/perf/graphics_2d/backend_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/graphics_2d/backend_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/graphics_2d/backend_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/graphics_2d/backend_probe_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/graphics_2d/backend_probe_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes, renders, and reads back without fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/backend_probe_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes CUDA when initialized or reports structured unavailability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/backend_probe_spec.spl:219:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes Vulkan SPIR-V when initialized or reports structured unavailability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
