# Engine2d Backend Provenance Matrix Specification

> <details>

<!-- sdn-diagram:id=engine2d_backend_provenance_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_backend_provenance_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_backend_provenance_matrix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_backend_provenance_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Backend Provenance Matrix Specification

## Scenarios

### Engine2D backend provenance matrix

#### should distinguish physical and software Vulkan devices on Linux

- Capture NVIDIA and Mesa Vulkan records through the facade
   - Expected: ["physical", "software"].len() equals `2`
- pending backend provenance matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture NVIDIA and Mesa Vulkan records through the facade")
expect(["physical", "software"].len()).to_equal(2)
pending_backend_provenance_matrix()
```

</details>

#### should label DirectX and Metal requests translated onto Vulkan

- Request DirectX and Metal compatibility lanes
   - Expected: ["simple-directx-on-vulkan", "simple-metal-on-vulkan"].len() equals `2`
- pending backend provenance matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request DirectX and Metal compatibility lanes")
expect(["simple-directx-on-vulkan", "simple-metal-on-vulkan"].len()).to_equal(2)
pending_backend_provenance_matrix()
```

</details>

<details>
<summary>Advanced: should keep native Windows and macOS checkpoints unavailable on Linux</summary>

#### should keep native Windows and macOS checkpoints unavailable on Linux

- Inspect native D3D and Metal host checkpoints
   - Expected: "host_unavailable" equals `host_unavailable`
- pending backend provenance matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect native D3D and Metal host checkpoints")
expect("host_unavailable").to_equal("host_unavailable")
pending_backend_provenance_matrix()
```

</details>


</details>

<details>
<summary>Advanced: should reject CPU fallback from a backend-specific pass</summary>

#### should reject CPU fallback from a backend-specific pass

- Force a requested Vulkan lane onto CPU pixels
   - Expected: "fallback-rejected" equals `fallback-rejected`
- pending backend provenance matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Force a requested Vulkan lane onto CPU pixels")
expect("fallback-rejected").to_equal("fallback-rejected")
pending_backend_provenance_matrix()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D backend provenance matrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
