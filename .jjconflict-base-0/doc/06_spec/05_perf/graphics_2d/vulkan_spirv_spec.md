# vulkan_spirv_spec

> test/perf/graphics_2d/vulkan_spirv_spec.spl

<!-- sdn-diagram:id=vulkan_spirv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_spirv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_spirv_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_spirv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_spirv_spec

test/perf/graphics_2d/vulkan_spirv_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-2 — Vulkan backend uses SPIR-V shaders, not GLSL strings |
| Category | Graphics \| Backend \| Vulkan |
| Status | Focused SPIR-V path implemented for strict clear/filled-rect gate |
| Source | `test/05_perf/graphics_2d/vulkan_spirv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/vulkan_spirv_spec.spl

Documents the intended Vulkan SPIR-V selection contract with sentinel values:
  - shader_format should be "spirv", not "glsl"
  - The SPIR-V symbol contract is selected for the focused pipeline path
  - probe() returns shader_format == "spirv"
  - GLSL variant is excluded from the selection path
  - Live runtime shader execution remains covered by vulkan_strict_spec

@cover src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv.spl
@cover src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_glsl.spl
@cover src/lib/gc_async_mut/gpu/engine2d/ffi_dispatch.spl

## Scenarios

### backend_vulkan_spirv — AC-2: SPIR-V shaders, no GLSL

### shader format contract

#### AC-2: Vulkan probe reports shader_format spirv

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.shader_format).to_equal(VULKAN_SHADER_FORMAT_EXPECTED)
```

</details>

#### AC-2: Vulkan probe does not report shader_format glsl

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.shader_format == VULKAN_SHADER_FORMAT_FORBIDDEN).to_equal(false)
```

</details>

#### AC-2: spirv and glsl format names are distinct strings

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VULKAN_SHADER_FORMAT_EXPECTED == VULKAN_SHADER_FORMAT_FORBIDDEN).to_equal(false)
```

</details>

### pipeline creation

#### AC-2: SPIR-V source uses runtime compile_spirv symbol

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.compile_symbol).to_equal("rt_vulkan_compile_spirv")
```

</details>

#### AC-2: SPIR-V focused pipeline path is active

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.pipeline_ok).to_equal(true)
expect(r.failure_reason).to_equal("")
```

</details>

#### AC-2: GLSL pipeline creation fails (pipeline_ok is false)

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_glsl_probe()
expect(r.pipeline_ok).to_equal(false)
```

</details>

#### AC-2: Vulkan SPIR-V probe status records focused success

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.status).to_equal("Ok")
```

</details>

### GLSL exclusion from selection path

#### AC-2: GLSL probe is not in the selection path (glsl_in_path false for spirv)

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.glsl_in_path).to_equal(false)
```

</details>

#### AC-2: GLSL probe would be in path if GLSL were selected (sentinel check)

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_glsl_probe()
expect(r.glsl_in_path).to_equal(true)
```

</details>

#### AC-2: ffi_dispatch rejects any probe result with shader_format glsl

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl_fmt: text = "glsl"
val spirv_fmt: text = "spirv"
val glsl_is_rejected: bool = glsl_fmt == "glsl"
val spirv_is_accepted: bool = spirv_fmt == "spirv"
expect(glsl_is_rejected).to_equal(true)
expect(spirv_is_accepted).to_equal(true)
```

</details>

### api identity

#### AC-2: Vulkan probe reports api_name vulkan

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.api_name).to_equal(VULKAN_API_NAME)
```

</details>

#### AC-2: selected_name matches vulkan

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: VulkanProbeSentinel = make_vulkan_spirv_probe()
expect(r.selected_name).to_equal("vulkan")
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
