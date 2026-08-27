# Compute Run Specification

> Tests covering compute_run end-to-end pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compute Run Specification

## Scenarios

### compute_run end-to-end pipeline

#### launch plan: grid = ceil(n / 256)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launch plan: grid = ceil(n / 256)
   - Expected: compute_grid_for(0) equals `0`
   - Expected: compute_grid_for(1) equals `1`
   - Expected: compute_grid_for(256) equals `1`
   - Expected: compute_grid_for(257) equals `2`
   - Expected: compute_grid_for(512) equals `2`
   - Expected: compute_grid_for(513) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("launch plan: grid = ceil(n / 256)")
expect(compute_grid_for(0)).to_equal(0)
expect(compute_grid_for(1)).to_equal(1)
expect(compute_grid_for(256)).to_equal(1)
expect(compute_grid_for(257)).to_equal(2)
expect(compute_grid_for(512)).to_equal(2)
expect(compute_grid_for(513)).to_equal(3)
```

</details>

#### cpu reference scales each element

- cpu reference scales each element
   - Expected: out.len() equals `3`
   - Expected: out[0] equals `4.0`
   - Expected: out[1] equals `6.0`
   - Expected: out[2] equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cpu reference scales each element")
val out = cpu_transform_scale_f32([2.0, 3.0, 4.0], 2.0)
expect(out.len()).to_equal(3)
expect(out[0]).to_equal(4.0)
expect(out[1]).to_equal(6.0)
expect(out[2]).to_equal(8.0)
```

</details>

#### cpu target runs on CPU with scalar backend

- cpu target runs on CPU with scalar backend
   - Expected: r.backend equals `scalar`
   - Expected: r.grid_x equals `1`
   - Expected: r.block_x equals `256`
   - Expected: r.data[1] equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cpu target runs on CPU with scalar backend")
val r = run_transform_scale_f32([2.0, 3.0, 4.0], 2.0, cpu_target())
expect(r.ran_on_cpu).to_be(true)
expect(r.backend).to_equal("scalar")
expect(r.grid_x).to_equal(1)
expect(r.block_x).to_equal(256)
expect(r.data[1]).to_equal(6.0)
```

</details>

#### cuda target with NO device falls back to CPU (no false gpu-ran claim)

- cuda target with NO device falls back to CPU (no false gpu-ran claim)
   - Expected: r.backend equals `cuda`
   - Expected: r.device_count equals `0`
   - Expected: r.data[2] equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cuda target with NO device falls back to CPU (no false gpu-ran claim)")
val r = run_transform_scale_f32([2.0, 3.0, 4.0], 2.0, cuda_target())
expect(r.backend).to_equal("cuda")
expect(r.device_count).to_equal(0)
expect(r.ran_on_cpu).to_be(true)
expect(r.data[2]).to_equal(8.0)
```

</details>

#### result preserves input length

- result preserves input length
   - Expected: r.data.len() equals `5`
   - Expected: r.data[4] equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("result preserves input length")
val r = run_transform_scale_f32([1.0, 1.0, 1.0, 1.0, 1.0], 3.0, cpu_target())
expect(r.data.len()).to_equal(5)
expect(r.data[4]).to_equal(3.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compute_run end-to-end pipeline.
- compute_run end-to-end pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `85844977f4725dc07a3854ad879a32ab391a3eff9ad6d351756b7586a2d4cca4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85844977f4725dc07a3854ad879a32ab391a3eff9ad6d351756b7586a2d4cca4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85844977f4725dc07a3854ad879a32ab391a3eff9ad6d351756b7586a2d4cca4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/compute/compute_run_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/compute/compute_run_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/compute/compute_run_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launch plan: grid = ceil(n / 256)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu reference scales each element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/compute/compute_run_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu target runs on CPU with scalar backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
