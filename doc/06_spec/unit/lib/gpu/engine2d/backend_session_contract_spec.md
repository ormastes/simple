# Backend Session Contract Specification

## Scenarios

### Engine2D backend session compute contract

#### exposes compute backend kinds for the shared session plan

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/backend_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D backend session compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

