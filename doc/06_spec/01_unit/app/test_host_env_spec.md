# Test Host Env Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Host Env Specification

## Scenarios

### test host environment SIMD evidence

<details>
<summary>Advanced: keeps a missing native SIMD row bound to the matrix evidence source</summary>

#### keeps a missing native SIMD row bound to the matrix evidence source

- "HostCapabilityRow create
   - Expected: source does not contain `if env.validation_reason() == "":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/test/test_host_env.spl")

expect(source).to_contain(
    "host-or-executed-path-required\", SIMD_MATRIX_PATH")
expect(source).to_contain(
    "val SIMD_MATRIX_PATH = \"build/cpu-simd-engine2d-arch-matrix/evidence.env\"")
expect(source).to_contain(
    "val CPU_SIMD_PATH = \"build/cpu-simd-engine2d-evidence/evidence.env\"")
expect(source).to_contain("if host_x86_simd_evidence_passes(cpu_simd):")
expect(source).to_contain(
    "HostCapabilityRow.create(\"x86_simd\", \"pass\", \"\", CPU_SIMD_PATH, \"\")")
expect(source).to_contain("if env.ready():")
expect(source.contains("if env.validation_reason() == \"\":")).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_host_env_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test host environment SIMD evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
