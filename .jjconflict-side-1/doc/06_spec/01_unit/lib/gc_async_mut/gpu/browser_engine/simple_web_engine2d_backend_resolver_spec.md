# Simple Web Engine2d Backend Resolver Specification

> <details>

<!-- sdn-diagram:id=simple_web_engine2d_backend_resolver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_engine2d_backend_resolver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_engine2d_backend_resolver_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_engine2d_backend_resolver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2d Backend Resolver Specification

## Scenarios

### Simple Web Engine2D backend resolver

#### routes auto through Engine2D native first detection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_web_engine2d_resolved_backend_name(40, 24, "auto").len()).to_be_greater_than(0)
```

</details>

#### preserves DirectX backend requests and UI aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_web_engine2d_resolved_backend_name(40, 24, "directx")).to_equal("directx")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "d3d11")).to_equal("directx")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "dx11")).to_equal("directx")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "dx12")).to_equal("directx")
```

</details>

#### preserves shared HIP and CPU SIMD aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_web_engine2d_resolved_backend_name(40, 24, "hip")).to_equal("rocm")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "amd-rocm")).to_equal("rocm")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "simd-cpu")).to_equal("cpu_simd")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "cpu-simd")).to_equal("cpu_simd")
```

</details>

#### still falls back unknown backend names to deterministic software

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_web_engine2d_resolved_backend_name(40, 24, "unknown-directx-like")).to_equal("software")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web Engine2D backend resolver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
