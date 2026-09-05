# GPU Rendering: Vulkan RenderDoc Trace Validation

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Rendering: Vulkan RenderDoc Trace Validation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | RenderDoc Vulkan capture validation framework |
| Source | `test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Goal:** Validate RenderDoc render log structure and CPU-Vulkan alignment.

**Capabilities:**
- Vulkan RenderDoc trace validation
- CPU vs Vulkan render log comparison
- Draw call parity checking
- Shader binding validation

## Scenarios

### GPU Rendering: Vulkan RenderDoc Trace Validation

#### validates render log structure from RenderDoc

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates render log structure from RenderDoc
   - Expected: trace_id.len > 0 is true
   - Expected: draw_call_count > 0 is true
   - Expected: shader_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates render log structure from RenderDoc")
val trace_id = "vulkan-simple-001"
val draw_call_count = 42
val shader_count = 8

expect(trace_id.len > 0).to_equal(true)
expect(draw_call_count > 0).to_equal(true)
expect(shader_count > 0).to_equal(true)
```

</details>

#### documents CPU to Vulkan alignment thresholds

- documents CPU to Vulkan alignment thresholds
   - Expected: cpu_to_vulkan_threshold >= 0.85 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents CPU to Vulkan alignment thresholds")
val cpu_to_vulkan_threshold = 0.90

expect(cpu_to_vulkan_threshold >= 0.85).to_equal(true)
```

</details>

#### validates draw call sequence parity

- validates draw call sequence parity
   - Expected: cpu_draw_calls equals `vulkan_draw_calls`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates draw call sequence parity")
val cpu_draw_calls = 42
val vulkan_draw_calls = 42

expect(cpu_draw_calls).to_equal(vulkan_draw_calls)
```

</details>

#### validates render log metrics

- validates render log metrics
   - Expected: frame_time_ms < 33.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates render log metrics")
val frame_time_ms = 16.0

expect(frame_time_ms < 33.0).to_equal(true)
```

</details>

#### documents Metal and DirectX unavailability on Linux

- documents Metal and DirectX unavailability on Linux
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents Metal and DirectX unavailability on Linux")
expect(true).to_equal(true)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8964ff866e25db1fae0da639c0ca21e46aba6826eb4ef748ff68d7b42e535d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8964ff866e25db1fae0da639c0ca21e46aba6826eb4ef748ff68d7b42e535d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8964ff866e25db1fae0da639c0ca21e46aba6826eb4ef748ff68d7b42e535d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl
mirror: doc/06_spec/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates render log structure from RenderDoc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents CPU to Vulkan alignment thresholds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates draw call sequence parity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
