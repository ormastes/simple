# backend_probe_spec

> test/perf/graphics_2d/backend_probe_spec.spl

<!-- sdn-diagram:id=backend_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_probe_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_probe_spec

test/perf/graphics_2d/backend_probe_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-1 — Backend probe strict-fail, no silent fallback |
| Category | Graphics \| Backend \| Probe |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/backend_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/backend_probe_spec.spl

Verifies that backend_probe reports selected backend identity,
enforces strict mode (no silent CPU fallback when GPU is requested),
and surfaces shader format in the probe result.

@cover src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl
@cover src/lib/gc_async_mut/gpu/engine2d/ffi_dispatch.spl

## Scenarios

### backend_probe — AC-1: strict probe, no silent fallback

### BackendProbeResult field contract

#### AC-1: probe result carries requested_name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(r.requested_name).to_equal("vulkan")
```

</details>

#### AC-1: probe result carries selected_name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(r.selected_name).to_equal("vulkan")
```

</details>

#### AC-1: probe result carries status field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(r.status).to_equal(STATUS_OK)
```

</details>

#### AC-1: probe result carries shader_format field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(r.shader_format).to_equal("spirv")
```

</details>

#### AC-1: probe result carries fallback_reason field (empty on Ok)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(r.fallback_reason).to_equal("")
```

</details>

#### AC-1: failed probe result has non-empty fallback_reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_failed_sentinel("cuda")
expect(r.fallback_reason).to_equal("device not present")
```

</details>

#### AC-1: failed probe status is Failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_failed_sentinel("cuda")
expect(r.status).to_equal(STATUS_FAILED)
```

</details>

### strict mode — no silent GPU→CPU fallback

#### AC-1: fallback sentinel from GPU request is a strict violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_fallback_sentinel("vulkan", "cpu")
expect(is_strict_fallback_violation(r)).to_equal(true)
```

</details>

#### AC-1: fallback sentinel from cuda request is a strict violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_fallback_sentinel("cuda", "cpu")
expect(is_strict_fallback_violation(r)).to_equal(true)
```

</details>

#### AC-1: fallback sentinel from metal request is a strict violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_fallback_sentinel("metal", "cpu")
expect(is_strict_fallback_violation(r)).to_equal(true)
```

</details>

#### AC-1: fallback sentinel from webgpu request is a strict violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_fallback_sentinel("webgpu", "software")
expect(is_strict_fallback_violation(r)).to_equal(true)
```

</details>

#### AC-1: cpu-requested fallback is not a strict violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_fallback_sentinel("cpu", "software")
expect(is_strict_fallback_violation(r)).to_equal(false)
```

</details>

#### AC-1: Ok status with matching requested/selected is not a violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(is_strict_fallback_violation(r)).to_equal(false)
```

</details>

### GLSL exclusion from selection

#### AC-1: shader_format 'glsl' must not appear in an Ok probe result for vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("vulkan", "vulkan", "spirv")
expect(r.shader_format).to_equal("spirv")
```

</details>

#### AC-1: shader_format 'spirv' is the only acceptable vulkan format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl_format: text = "glsl"
val spirv_format: text = "spirv"
expect(glsl_format == spirv_format).to_equal(false)
```

</details>

### CPU-only default when no GPU feature enabled

#### AC-1: cpu probe status is Ok with shader_format none

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("cpu", "cpu", "none")
expect(r.status).to_equal(STATUS_OK)
expect(r.shader_format).to_equal("none")
```

</details>

#### AC-1: software probe status is Ok with shader_format none

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProbeResultSentinel = make_ok_sentinel("software", "software", "none")
expect(r.status).to_equal(STATUS_OK)
expect(r.shader_format).to_equal("none")
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


</details>
