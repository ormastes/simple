# Engine2D OpenCL Session Lifecycle Evidence Specification

> Verifies typed OpenCL session lifecycle evidence for unavailable runtime paths and generated 2D launch evidence, including plan-not-ready and missing-argument diagnostics.

<!-- sdn-diagram:id=opencl_session_lifecycle_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opencl_session_lifecycle_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opencl_session_lifecycle_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opencl_session_lifecycle_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D OpenCL Session Lifecycle Evidence Specification

Verifies typed OpenCL session lifecycle evidence for unavailable runtime paths and generated 2D launch evidence, including plan-not-ready and missing-argument diagnostics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Reference | `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl` |
| Requirements | N/A |
| Plan | doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md |
| Design | doc/05_design/ui/renderer_unification_2026-06-15.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md |
| Source | `test/01_unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.spl` |
| Updated | 2026-06-21 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies typed OpenCL session lifecycle evidence for unavailable runtime paths
and generated 2D launch evidence, including plan-not-ready and missing-argument
diagnostics.

**Source:** `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl`
**Requirements:** N/A
**Research:** doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md
**Plan:** doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md
**Design:** doc/05_design/ui/renderer_unification_2026-06-15.md

## Syntax

Use `init_evidence()`, `load_module_evidence()`,
`launch_kernel_evidence()`, `synchronize_evidence()`, and
`launch_generated_2d_evidence()` to inspect typed failure evidence without
parsing logs.

## Examples

The scenarios cover missing OpenCL FFI lifecycle diagnostics and generated 2D
operation evidence for fill, copy, alpha blend, scroll, rectangle fill,
missing arguments, and invalid dimensions.

## Scenarios

### OpenClSession lifecycle evidence

#### reports typed lifecycle evidence for unavailable OpenCL runtime paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

val init_ev = session.init_evidence()
val load_ev = session.load_module_evidence("opencl-source")
val launch_ev = session.launch_kernel_evidence("simple_2d_fill_u32", 1, 1, 1, 1)
val sync_ev = session.synchronize_evidence()

expect(init_ev.success).to_equal(false)
expect(init_ev.status_code).to_equal("missing-ffi")
expect(init_ev.reason).to_equal("missing-opencl-ffi")
expect(load_ev.status_code).to_equal("missing-ffi")
expect(launch_ev.status_code).to_equal("missing-ffi")
expect(sync_ev.status_code).to_equal("missing-ffi")
expect(sync_ev.diagnostic_text()).to_contain("OpenClSessionEvidence")
```

</details>

#### reports typed generated 2D launch evidence for generated OpenCL dispatch operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

val fill_ev = session.launch_generated_2d_evidence("fill", 16, 16, 4096)
val copy_ev = session.launch_generated_2d_evidence("copy", 16, 16, 4096)
val alpha_ev = session.launch_generated_2d_evidence("alpha_blend", 16, 16, 4096)
val scroll_ev = session.launch_generated_2d_evidence("scroll", 16, 16, 4096)
val rect_ev = session.launch_generated_2d_evidence("rect_filled", 16, 16, 4096)
val missing_args_ev = session.launch_generated_2d_evidence("fill", 16, 16, 0)
val bad_plan_ev = session.launch_generated_2d_evidence("fill", 0, 16, 4096)

expect(fill_ev.operation).to_equal("launch_generated_2d:fill")
expect(fill_ev.status_code).to_equal("missing-ffi")
expect(copy_ev.operation).to_equal("launch_generated_2d:copy")
expect(copy_ev.status_code).to_equal("missing-ffi")
expect(alpha_ev.operation).to_equal("launch_generated_2d:alpha_blend")
expect(alpha_ev.status_code).to_equal("missing-ffi")
expect(scroll_ev.operation).to_equal("launch_generated_2d:scroll")
expect(scroll_ev.status_code).to_equal("missing-ffi")
expect(rect_ev.operation).to_equal("launch_generated_2d:rect_filled")
expect(rect_ev.status_code).to_equal("plan-not-ready")
expect(rect_ev.reason).to_equal("unsupported-operation")
expect(missing_args_ev.status_code).to_equal("missing-args-pointer")
expect(bad_plan_ev.status_code).to_equal("plan-not-ready")
expect(bad_plan_ev.reason).to_equal("invalid-dimensions")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md](doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md)
- **Design:** [doc/05_design/ui/renderer_unification_2026-06-15.md](doc/05_design/ui/renderer_unification_2026-06-15.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md](doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md)


</details>
