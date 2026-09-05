# Cuda Provider Smoke Specification

> Tests covering cuda_provider smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Provider Smoke Specification

## Scenarios

### cuda_provider smoke

#### provider names are correct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- provider names are correct
   - Expected: provider_name(Provider.MockBackend) equals `mock`
   - Expected: provider_name(Provider.CpuBackend) equals `cpu`
   - Expected: provider_name(Provider.CudaBackend) equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("provider names are correct")
expect(provider_name(Provider.MockBackend)).to_equal("mock")
expect(provider_name(Provider.CpuBackend)).to_equal("cpu")
expect(provider_name(Provider.CudaBackend)).to_equal("cuda")
```

</details>

#### is_real_native is false for mock, true for cpu and cuda

- is_real_native is false for mock, true for cpu and cuda
   - Expected: provider_is_real_native(Provider.MockBackend) is false
   - Expected: provider_is_real_native(Provider.CpuBackend) is true
   - Expected: provider_is_real_native(Provider.CudaBackend) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_real_native is false for mock, true for cpu and cuda")
expect(provider_is_real_native(Provider.MockBackend)).to_equal(false)
expect(provider_is_real_native(Provider.CpuBackend)).to_equal(true)
expect(provider_is_real_native(Provider.CudaBackend)).to_equal(true)
```

</details>

#### requires device memory only for cuda

- requires device memory only for cuda
   - Expected: provider_requires_device_memory(Provider.MockBackend) is false
   - Expected: provider_requires_device_memory(Provider.CpuBackend) is false
   - Expected: provider_requires_device_memory(Provider.CudaBackend) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("requires device memory only for cuda")
expect(provider_requires_device_memory(Provider.MockBackend)).to_equal(false)
expect(provider_requires_device_memory(Provider.CpuBackend)).to_equal(false)
expect(provider_requires_device_memory(Provider.CudaBackend)).to_equal(true)
```

</details>

#### select_provider: mock when requested

- select_provider: mock when requested
   - Expected: provider_name(select_provider("mock", true, true)) equals `mock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: mock when requested")
expect(provider_name(select_provider("mock", true, true))).to_equal("mock")
```

</details>

#### select_provider: cuda when requested and available

- select_provider: cuda when requested and available
   - Expected: provider_name(select_provider("cuda", true, false)) equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: cuda when requested and available")
expect(provider_name(select_provider("cuda", true, false))).to_equal("cuda")
```

</details>

#### select_provider: mock fallback when cuda requested but unavailable

- select_provider: mock fallback when cuda requested but unavailable
   - Expected: provider_name(select_provider("cuda", false, false)) equals `mock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: mock fallback when cuda requested but unavailable")
expect(provider_name(select_provider("cuda", false, false))).to_equal("mock")
```

</details>

#### select_provider: cpu when openblas requested and available

- select_provider: cpu when openblas requested and available
   - Expected: provider_name(select_provider("openblas", false, true)) equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: cpu when openblas requested and available")
expect(provider_name(select_provider("openblas", false, true))).to_equal("cpu")
```

</details>

#### select_provider: auto picks cuda first

- select_provider: auto picks cuda first
   - Expected: provider_name(select_provider("auto", true, true)) equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: auto picks cuda first")
expect(provider_name(select_provider("auto", true, true))).to_equal("cuda")
```

</details>

#### select_provider: auto picks cpu when cuda unavailable

- select_provider: auto picks cpu when cuda unavailable
   - Expected: provider_name(select_provider("auto", false, true)) equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: auto picks cpu when cuda unavailable")
expect(provider_name(select_provider("auto", false, true))).to_equal("cpu")
```

</details>

#### select_provider: auto falls back to mock

- select_provider: auto falls back to mock
   - Expected: provider_name(select_provider("auto", false, false)) equals `mock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("select_provider: auto falls back to mock")
expect(provider_name(select_provider("auto", false, false))).to_equal("mock")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/cuda_provider_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cuda_provider smoke.
- cuda_provider smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80388a5084e0fcb365d1040379def5dc288e632915a68076971cf9759e3a4bd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80388a5084e0fcb365d1040379def5dc288e632915a68076971cf9759e3a4bd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80388a5084e0fcb365d1040379def5dc288e632915a68076971cf9759e3a4bd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/cuda_provider_smoke_spec.spl
mirror: doc/06_spec/feature/scilib/cuda_provider_smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/cuda_provider_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/cuda_provider_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/cuda_provider_smoke_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provider names are correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/cuda_provider_smoke_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_real_native is false for mock, true for cpu and cuda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/cuda_provider_smoke_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires device memory only for cuda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
