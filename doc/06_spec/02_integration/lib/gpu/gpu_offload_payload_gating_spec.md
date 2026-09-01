# GPU Offload Payload-Gating Discriminator

> A claim that work ran on the GPU must be *discriminated*, not merely observed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Offload Payload-Gating Discriminator

A claim that work ran on the GPU must be *discriminated*, not merely observed.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A claim that work ran on the GPU must be *discriminated*, not merely observed.
One honest gate is proven here across backends:

1. **std.compute** is a payload-gated simulation: it always computes the CPU
   reference and only reports GPU provenance. With no payload the CPU ran; with
   a payload the provenance flips — the value must equal the CPU oracle in
   BOTH branches. ExecTarget enforcement is proven too: `suggest` falls back
   (resolved), `require` of an absent GPU fails closed (unresolved).
Every backend runs the SAME shared body, so backend coverage is data-driven.

## Scenarios

### compute-surface payload gating per backend

#### gates CUDA offload on the payload without changing the value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gates CUDA offload on the payload without changing the value
- Dispatch a reduce on a CUDA target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates CUDA offload on the payload without changing the value")
step("Dispatch a reduce on a CUDA target with and without a payload")
assert_payload_gating(ComputeBackend.Cuda)
```

</details>

#### gates HIP offload on the payload without changing the value

- gates HIP offload on the payload without changing the value
- Dispatch a reduce on a HIP target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates HIP offload on the payload without changing the value")
step("Dispatch a reduce on a HIP target with and without a payload")
assert_payload_gating(ComputeBackend.Hip)
```

</details>

#### gates OpenCL offload on the payload without changing the value

- gates OpenCL offload on the payload without changing the value
- Dispatch a reduce on an OpenCL target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates OpenCL offload on the payload without changing the value")
step("Dispatch a reduce on an OpenCL target with and without a payload")
assert_payload_gating(ComputeBackend.OpenCl)
```

</details>

#### gates Vulkan offload on the payload without changing the value

- gates Vulkan offload on the payload without changing the value
- Dispatch a reduce on a Vulkan target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates Vulkan offload on the payload without changing the value")
step("Dispatch a reduce on a Vulkan target with and without a payload")
assert_payload_gating(ComputeBackend.Vulkan)
```

</details>

#### gates Metal offload on the payload without changing the value

- gates Metal offload on the payload without changing the value
- Dispatch a reduce on a Metal target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates Metal offload on the payload without changing the value")
step("Dispatch a reduce on a Metal target with and without a payload")
assert_payload_gating(ComputeBackend.Metal)
```

</details>

#### gates WebGPU offload on the payload without changing the value

- gates WebGPU offload on the payload without changing the value
- Dispatch a reduce on a WebGPU target with and without a payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates WebGPU offload on the payload without changing the value")
step("Dispatch a reduce on a WebGPU target with and without a payload")
assert_payload_gating(ComputeBackend.WebGpu)
```

</details>

### ExecTarget enforcement

#### suggests a GPU class and falls back to CPU on a bare machine

- suggests a GPU class and falls back to CPU on a bare machine
- Resolve a GPU class in SUGGEST mode with no GPU caps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("suggests a GPU class and falls back to CPU on a bare machine")
step("Resolve a GPU class in SUGGEST mode with no GPU caps")
assert_suggest_falls_back()
```

</details>

#### requires a GPU class and fails closed on a bare machine

- requires a GPU class and fails closed on a bare machine
- Resolve a GPU class in REQUIRE mode with no GPU caps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("requires a GPU class and fails closed on a bare machine")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fcebca869aa119cb96ba25c90cba028a0b4cff1d56b6670940b09bd69d5305cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcebca869aa119cb96ba25c90cba028a0b4cff1d56b6670940b09bd69d5305cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcebca869aa119cb96ba25c90cba028a0b4cff1d56b6670940b09bd69d5305cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/gpu_offload_payload_gating_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates CUDA offload on the payload without changing the value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates HIP offload on the payload without changing the value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates OpenCL offload on the payload without changing the value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
