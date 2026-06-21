# Engine2D Backend Session Contract Specification

> Verifies the public Engine2D backend-session names used by the shared compute plan, including CPU SIMD, HIP/ROCm, OpenCL, Qualcomm, and CUDA aliases.

<!-- sdn-diagram:id=backend_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Backend Session Contract Specification

Verifies the public Engine2D backend-session names used by the shared compute plan, including CPU SIMD, HIP/ROCm, OpenCL, Qualcomm, and CUDA aliases.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Reference | `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl` |
| Requirements | N/A |
| Plan | doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md |
| Design | doc/05_design/ui/renderer_unification_2026-06-15.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md |
| Source | `test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the public Engine2D backend-session names used by the shared compute
plan, including CPU SIMD, HIP/ROCm, OpenCL, Qualcomm, and CUDA aliases.

**Source:** `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl`
**Source:** `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl`
**Requirements:** N/A
**Research:** doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md
**Plan:** doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md
**Design:** doc/05_design/ui/renderer_unification_2026-06-15.md

## Syntax

Use `BackendSessionKind` factories and `resolved_kind_name(...)` when callers
need stable backend-session names instead of parsing backend strings.

## Examples

The scenarios verify backend kind factories, public backend-name resolution, and
portable compute error fields for unavailable backends.

## Scenarios

### Engine2D backend session compute contract

#### exposes compute backend kinds for the shared session plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BackendSessionKind.cpu_simd().kind).to_equal("cpu_simd")
expect(BackendSessionKind.hip().kind).to_equal("hip")
expect(BackendSessionKind.rocm().kind).to_equal("rocm")
expect(BackendSessionKind.opencl().kind).to_equal("opencl")
expect(BackendSessionKind.qualcomm().kind).to_equal("qualcomm")
expect(backend_session_kind_name(BackendSessionKind.opencl())).to_equal("opencl")
```

</details>

#### maps public backend names to session kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolved_kind_name("cpu_simd")).to_equal("cpu_simd")
expect(resolved_kind_name("hip")).to_equal("hip")
expect(resolved_kind_name("rocm")).to_equal("rocm")
expect(resolved_kind_name("opencl")).to_equal("opencl")
expect(resolved_kind_name("qualcomm")).to_equal("qualcomm")
expect(resolved_kind_name("cuda")).to_equal("cuda")
```

</details>

#### carries portable compute errors for unavailable backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = compute_error_unavailable(BackendSessionKind.opencl(), "missing OpenCL ICD")

expect(err.kind).to_equal("opencl")
expect(err.code).to_equal(1)
expect(err.message).to_equal("missing OpenCL ICD")
expect(err.is_ok()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md](doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md)
- **Design:** [doc/05_design/ui/renderer_unification_2026-06-15.md](doc/05_design/ui/renderer_unification_2026-06-15.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md](doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md)


</details>
