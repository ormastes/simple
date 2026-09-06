# Gpu Backend Shared Interface Parity Specification

> <details>

<!-- sdn-diagram:id=gpu_backend_shared_interface_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_backend_shared_interface_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_backend_shared_interface_parity_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_backend_shared_interface_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Backend Shared Interface Parity Specification

## Scenarios

### GPU backend shared artifact schema parity

#### requires CUDA Vulkan Metal OpenCL and HIP generated artifact rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = gpu_artifact_schema_parity_rows()

expect(rows.len()).to_equal(5)
expect(rows[0].backend_family).to_equal("cuda")
expect(rows[1].backend_family).to_equal("vulkan")
expect(rows[2].backend_family).to_equal("metal")
expect(rows[3].backend_family).to_equal("opencl")
expect(rows[4].backend_family).to_equal("hip")
expect(rows[1].source_format).to_equal("spirv")
expect(rows[1].binary_format).to_equal("spirv")
expect(rows[1].tool_hint).to_equal("vulkan-spirv-runtime")
expect(rows[1].artifact_path_suffix).to_equal("build/gpu/vulkan/simple_2d.spirv")
expect(rows[1].required_symbols).to_contain("simple_2d_bitmap_glyph_raster_u32")
expect(rows[2].source_format).to_equal("metal-shading-language")
expect(rows[2].binary_format).to_equal("metallib")
expect(rows[2].artifact_path_suffix).to_equal("build/gpu/metal/simple_2d.metallib")
expect(rows[3].checksum_verified).to_be(true)
expect(gpu_artifact_schema_parity_rows_valid(rows)).to_be(true)
```

</details>

#### reports Vulkan and Metal in the shared artifact schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gpu_artifact_schema_parity_report_sdn(gpu_artifact_schema_parity_rows())

expect(report).to_contain("row_count: 5")
expect(report).to_contain("backend: \"vulkan\"")
expect(report).to_contain("backend: \"metal\"")
expect(report).to_contain("source_format: \"spirv\"")
expect(report).to_contain("source_format: \"metal-shading-language\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/gpu_backend_shared_interface_parity_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU backend shared artifact schema parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
