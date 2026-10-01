# Opencl Session Lifecycle Evidence Specification

> Tests covering OpenClSession lifecycle evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencl Session Lifecycle Evidence Specification

## Scenarios

### OpenClSession lifecycle evidence

#### reports typed lifecycle evidence for unavailable OpenCL runtime paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports typed lifecycle evidence for unavailable OpenCL runtime paths
   - Expected: init_ev.success is false
   - Expected: init_ev.status_code equals `missing-ffi`
   - Expected: init_ev.reason equals `missing-opencl-ffi`
   - Expected: load_ev.status_code equals `missing-ffi`
   - Expected: launch_ev.status_code equals `missing-ffi`
   - Expected: sync_ev.status_code equals `missing-ffi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports typed lifecycle evidence for unavailable OpenCL runtime paths")
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

- reports typed generated 2D launch evidence for generated OpenCL dispatch operations
   - Expected: fill_ev.operation equals `launch_generated_2d:fill`
   - Expected: fill_ev.status_code equals `missing-ffi`
   - Expected: copy_ev.operation equals `launch_generated_2d:copy`
   - Expected: copy_ev.status_code equals `missing-ffi`
   - Expected: alpha_ev.operation equals `launch_generated_2d:alpha_blend`
   - Expected: alpha_ev.status_code equals `missing-ffi`
   - Expected: scroll_ev.operation equals `launch_generated_2d:scroll`
   - Expected: scroll_ev.status_code equals `missing-ffi`
   - Expected: rect_ev.operation equals `launch_generated_2d:rect_filled`
   - Expected: rect_ev.status_code equals `plan-not-ready`
   - Expected: rect_ev.reason equals `unsupported-operation`
   - Expected: missing_args_ev.status_code equals `missing-args-pointer`
   - Expected: bad_plan_ev.status_code equals `plan-not-ready`
   - Expected: bad_plan_ev.reason equals `invalid-dimensions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports typed generated 2D launch evidence for generated OpenCL dispatch operations")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OpenClSession lifecycle evidence.
- OpenClSession lifecycle evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f97633b890fb69f43a1b4b6117ef5df60a592114f2c72fb587ac233bc5e5412a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f97633b890fb69f43a1b4b6117ef5df60a592114f2c72fb587ac233bc5e5412a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f97633b890fb69f43a1b4b6117ef5df60a592114f2c72fb587ac233bc5e5412a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/opencl_session_lifecycle_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
