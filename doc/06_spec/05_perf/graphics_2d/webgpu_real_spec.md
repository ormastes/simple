# webgpu_real_spec

> test/perf/graphics_2d/webgpu_real_spec.spl

<!-- sdn-diagram:id=webgpu_real_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_real_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_real_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_real_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webgpu_real_spec

test/perf/graphics_2d/webgpu_real_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-5 — WebGPU/wgpu real adapter enumeration, no silent CPU fallback |
| Category | Graphics \| Backend \| WebGPU |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/webgpu_real_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/webgpu_real_spec.spl

Verifies that the WebGPU/wgpu backend:
  - Enumerates adapters at startup
  - Does NOT fall through to CPU-only path silently
  - probe() reports shader_format == "wgsl"
  - selected_name reflects the actual adapter chosen

@cover src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl

## Scenarios

### backend_webgpu — AC-5: real adapter enumeration, no silent fallback

### WebGPU probe identity

#### AC-5: WebGPU probe reports backend name webgpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.backend).to_equal(WEBGPU_BACKEND_NAME)
```

</details>

#### AC-5: WebGPU probe reports shader_format wgsl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.shader_format).to_equal(WEBGPU_SHADER_FORMAT)
```

</details>

#### AC-5: WebGPU probe reports api_name wgpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.api_name).to_equal(WEBGPU_API_NAME)
```

</details>

#### AC-5: WebGPU status is Ok when adapter is found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.status).to_equal("Ok")
```

</details>

### adapter enumeration

#### AC-5: adapter_count is greater than zero when WebGPU is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.adapter_count > 0).to_equal(true)
```

</details>

#### AC-5: selected_adapter is non-empty when WebGPU is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.selected_adapter).to_equal("DiscreteGpu(NVIDIA GeForce RTX 3080)")
```

</details>

#### AC-5: adapter_count is zero when no GPU hardware is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_no_adapter()
expect(r.adapter_count).to_equal(0)
```

</details>

#### AC-5: status is Failed (not Fallback) when no adapters are enumerated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_no_adapter()
expect(r.status).to_equal("Failed")
```

</details>

### no silent CPU fallback

#### AC-5: fell_through_to_cpu is false when real WebGPU is selected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.fell_through_to_cpu).to_equal(false)
```

</details>

#### AC-5: silent fallback probe has fell_through_to_cpu true (sentinel for what is forbidden)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_silent_fallback()
expect(r.fell_through_to_cpu).to_equal(true)
```

</details>

#### AC-5: silent fallback status is Fallback (strict mode must reject this)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_silent_fallback()
expect(r.status).to_equal("Fallback")
```

</details>

#### AC-5: real WebGPU probe fallback_reason is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: WebGpuProbeSentinel = make_webgpu_real_probe()
expect(r.fallback_reason).to_equal("")
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
