# GPU Offload Payload-Gating Discriminator

> Verifies the gpu offload payload gating behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Offload Payload-Gating Discriminator

Verifies the gpu offload payload gating behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** In Progress |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the gpu offload payload gating behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### compute-surface payload gating per backend

#### gates CUDA offload on the payload without changing the value

- Verify: gates CUDA offload on the payload without changing the value
- Dispatch a reduce on a CUDA target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: gates CUDA offload on the payload without changing the value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Dispatch a reduce on a CUDA target with and without a payload")
assert_payload_gating(ComputeBackend.Cuda)
```

</details>

#### gates HIP offload on the payload without changing the value

- Verify: gates HIP offload on the payload without changing the value
- Dispatch a reduce on a HIP target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: gates HIP offload on the payload without changing the value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Dispatch a reduce on a HIP target with and without a payload")
assert_payload_gating(ComputeBackend.Hip)
```

</details>

#### gates OpenCL offload on the payload without changing the value

- Verify: gates OpenCL offload on the payload without changing the value
- Dispatch a reduce on an OpenCL target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: gates OpenCL offload on the payload without changing the value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Dispatch a reduce on an OpenCL target with and without a payload")
assert_payload_gating(ComputeBackend.OpenCl)
```

</details>

#### gates Vulkan offload on the payload without changing the value

- Verify: gates Vulkan offload on the payload without changing the value
- Dispatch a reduce on a Vulkan target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: gates Vulkan offload on the payload without changing the value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Dispatch a reduce on a Vulkan target with and without a payload")
assert_payload_gating(ComputeBackend.Vulkan)
```

</details>

#### gates Metal offload on the payload without changing the value

- Verify: gates Metal offload on the payload without changing the value
- Dispatch a reduce on a Metal target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: gates Metal offload on the payload without changing the value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Dispatch a reduce on a Metal target with and without a payload")
assert_payload_gating(ComputeBackend.Metal)
```

</details>

#### gates WebGPU offload on the payload without changing the value

- Verify: gates WebGPU offload on the payload without changing the value
- Dispatch a reduce on a WebGPU target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: gates WebGPU offload on the payload without changing the value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Dispatch a reduce on a WebGPU target with and without a payload")
assert_payload_gating(ComputeBackend.WebGpu)
```

</details>

### ExecTarget enforcement

#### suggests a GPU class and falls back to CPU on a bare machine

- Verify: suggests a GPU class and falls back to CPU on a bare machine
- Resolve a GPU class in SUGGEST mode with no GPU caps


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: suggests a GPU class and falls back to CPU on a bare machine")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Resolve a GPU class in SUGGEST mode with no GPU caps")
assert_suggest_falls_back()
```

</details>

#### requires a GPU class and fails closed on a bare machine

- Verify: requires a GPU class and fails closed on a bare machine
- Resolve a GPU class in REQUIRE mode with no GPU caps


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-GPU_GPU_OFFLOAD_PAYLOAD_GATI-001
step("Verify: requires a GPU class and fails closed on a bare machine")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Resolve a GPU class in REQUIRE mode with no GPU caps")
assert_require_absent_fails_closed()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3dd0ed7f381daf2692bc025f4a667850dda8379e7a7fa39a382db4d093e08c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3dd0ed7f381daf2692bc025f4a667850dda8379e7a7fa39a382db4d093e08c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3dd0ed7f381daf2692bc025f4a667850dda8379e7a7fa39a382db4d093e08c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
