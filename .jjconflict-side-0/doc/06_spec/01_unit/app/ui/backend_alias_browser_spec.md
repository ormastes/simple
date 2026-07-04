# Backend Alias Browser Specification

> <details>

<!-- sdn-diagram:id=backend_alias_browser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_alias_browser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_alias_browser_spec -> std
backend_alias_browser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_alias_browser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Alias Browser Specification

## Scenarios

### Browser backend aliases

#### preserves native and accelerated backend names through the browser adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BrowserBackend.create(64, 48, "metal").unwrap().gpu_backend()).to_equal("metal")
expect(BrowserBackend.create(64, 48, "cuda").unwrap().gpu_backend()).to_equal("cuda")
expect(BrowserBackend.create(64, 48, "hip").unwrap().gpu_backend()).to_equal("rocm")
expect(BrowserBackend.create(64, 48, "vulkan").unwrap().gpu_backend()).to_equal("vulkan")
expect(BrowserBackend.create(64, 48, "opencl").unwrap().gpu_backend()).to_equal("opencl")
```

</details>

#### preserves DirectX aliases as the DirectX backend lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BrowserBackend.create(64, 48, "directx").unwrap().gpu_backend()).to_equal("directx")
expect(BrowserBackend.create(64, 48, "dx11").unwrap().gpu_backend()).to_equal("directx")
expect(BrowserBackend.create(64, 48, "d3d11").unwrap().gpu_backend()).to_equal("directx")
```

</details>

#### preserves CPU SIMD aliases through the browser adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BrowserBackend.create(64, 48, "simd_cpu").unwrap().gpu_backend()).to_equal("cpu_simd")
expect(BrowserBackend.create(64, 48, "cpu-simd").unwrap().gpu_backend()).to_equal("cpu_simd")
```

</details>

#### uses the resolved auto backend for repeated pure Simple render frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _backend_alias_browser_state()
val backend = BrowserBackend.create(64, 48, "auto").unwrap()
val resolved = backend.gpu_backend()

expect(resolved.len()).to_be_greater_than(0)
expect(resolved).to_not_equal("auto")
expect(resolved).to_equal(web_render_resolved_engine2d_backend_name(1, 1, "auto"))

backend.render_frame(state.tree, state)
expect(backend.gpu_backend()).to_equal(resolved)
expect(backend.last_artifact_engine2d_backend).to_equal(resolved)

backend.resize(80, 48)
backend.render_frame(state.tree, state)
expect(backend.gpu_backend()).to_equal(resolved)
expect(backend.last_artifact_engine2d_backend).to_equal(resolved)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_alias_browser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser backend aliases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
