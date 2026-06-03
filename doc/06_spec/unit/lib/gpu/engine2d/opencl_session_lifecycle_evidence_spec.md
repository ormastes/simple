# Opencl Session Lifecycle Evidence Specification

## Scenarios

### OpenClSession lifecycle evidence

#### reports typed lifecycle evidence for unavailable OpenCL runtime paths

<details>
<summary>Executable SPipe</summary>

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

#### reports typed generated 2D launch evidence for all OpenCL operations

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

val fill_ev = session.launch_generated_2d_evidence("fill", 16, 16, 4096)
val copy_ev = session.launch_generated_2d_evidence("copy", 16, 16, 4096)
val alpha_ev = session.launch_generated_2d_evidence("alpha_blend", 16, 16, 4096)
val scroll_ev = session.launch_generated_2d_evidence("scroll", 16, 16, 4096)
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
expect(missing_args_ev.status_code).to_equal("missing-args-pointer")
expect(bad_plan_ev.status_code).to_equal("plan-not-ready")
expect(bad_plan_ev.reason).to_equal("invalid-dimensions")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenClSession lifecycle evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
