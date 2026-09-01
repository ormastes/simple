# Engine2D Backend Lane Order Parity

> Defect-class guard for the duplicated `gpu/engine2d/backend_lane` module. The `nogc_async_mut` copy silently drifted from the canonical `gc_async_mut` ordering contract: it dropped the explicit-native (`baremetal`/`virtio_gpu`) head, dropped `qualcomm`/`intel`, and returned a comma-joined list from `engine2d_backend_lane_preference_summary()` instead of the `>`-separated summary. Every caller that resolves `std.gpu.engine2d.backend_lane` got the stale order without any error.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Backend Lane Order Parity

Defect-class guard for the duplicated `gpu/engine2d/backend_lane` module. The `nogc_async_mut` copy silently drifted from the canonical `gc_async_mut` ordering contract: it dropped the explicit-native (`baremetal`/`virtio_gpu`) head, dropped `qualcomm`/`intel`, and returned a comma-joined list from `engine2d_backend_lane_preference_summary()` instead of the `>`-separated summary. Every caller that resolves `std.gpu.engine2d.backend_lane` got the stale order without any error.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #engine2d-backend-lane-order |
| Category | Unit / Graphics |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/gpu/engine2d_backend_lane_order_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Defect-class guard for the duplicated `gpu/engine2d/backend_lane` module. The
`nogc_async_mut` copy silently drifted from the canonical `gc_async_mut`
ordering contract: it dropped the explicit-native (`baremetal`/`virtio_gpu`)
head, dropped `qualcomm`/`intel`, and returned a comma-joined list from
`engine2d_backend_lane_preference_summary()` instead of the `>`-separated
summary. Every caller that resolves `std.gpu.engine2d.backend_lane` got the
stale order without any error.

This spec pins the ordering CONTRACT that both copies must satisfy, so a future
divergence in either family fails here instead of in a downstream perf gate.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** N/A

## Research

**Research:** N/A

## Scenarios

### engine2d backend lane order parity

#### keeps the full order explicit-native first and GPU-tier complete

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the full order explicit-native first and GPU-tier complete
   - Expected: full[0] equals `baremetal`
   - Expected: full[1] equals `virtio_gpu`
   - Expected: full[2] equals `metal`
   - Expected: full[full.len() - 1] equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("keeps the full order explicit-native first and GPU-tier complete")
val full = engine2d_backend_lane_full_preference_order()

expect(full[0]).to_equal("baremetal")
expect(full[1]).to_equal("virtio_gpu")
expect(full[2]).to_equal("metal")
expect(index_of(full, "qualcomm")).to_be_greater_than(0)
expect(index_of(full, "intel")).to_be_greater_than(0)
expect(full[full.len() - 1]).to_equal("cpu")
```

</details>

#### keeps the drawing order native-first without explicit-native surfaces

- keeps the drawing order native-first without explicit-native surfaces
   - Expected: drawing[0] equals `metal`
   - Expected: index_of(drawing, "baremetal") equals `-1`
   - Expected: index_of(drawing, "virtio_gpu") equals `-1`
   - Expected: drawing[drawing.len() - 1] equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("keeps the drawing order native-first without explicit-native surfaces")
val drawing = engine2d_backend_lane_drawing_preference_order()

expect(drawing[0]).to_equal("metal")
expect(index_of(drawing, "baremetal")).to_equal(-1)
expect(index_of(drawing, "virtio_gpu")).to_equal(-1)
expect(index_of(drawing, "cuda")).to_be_less_than(index_of(drawing, "vulkan"))
expect(index_of(drawing, "vulkan")).to_be_less_than(index_of(drawing, "directx"))
expect(index_of(drawing, "directx")).to_be_less_than(index_of(drawing, "opencl"))
expect(drawing[drawing.len() - 1]).to_equal("cpu")
```

</details>

#### keeps the summary a readable preference chain, not a joined list

- keeps the summary a readable preference chain, not a joined list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("keeps the summary a readable preference chain, not a joined list")
val summary = engine2d_backend_lane_preference_summary()

expect(summary).to_contain("vulkan > directx > opencl")
expect(summary).to_contain("baremetal")
expect(summary).to_contain("cpu_simd > software > cpu")
```

</details>

#### keeps drawing order and font-offload order tier-consistent

- keeps drawing order and font-offload order tier-consistent
   - Expected: index_of(font, "metal") equals `index_of(drawing, "metal")`
   - Expected: index_of(font, "cuda") equals `index_of(drawing, "cuda")`
   - Expected: index_of(font, "vulkan") equals `index_of(drawing, "vulkan")`
   - Expected: index_of(font, "cpu") equals `index_of(drawing, "cpu")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("keeps drawing order and font-offload order tier-consistent")
# Positive control: both orders must rank the same GPU tiers the same
# way, so a drift in either list is caught here.
val drawing = engine2d_backend_lane_drawing_preference_order()
val font = engine2d_font_offload_backend_order()

expect(index_of(font, "metal")).to_equal(index_of(drawing, "metal"))
expect(index_of(font, "cuda")).to_equal(index_of(drawing, "cuda"))
expect(index_of(font, "vulkan")).to_equal(index_of(drawing, "vulkan"))
expect(index_of(font, "cpu")).to_equal(index_of(drawing, "cpu"))
```

</details>

#### excludes explicit-native candidates from automatic selection

- excludes explicit-native candidates from automatic selection
   - Expected: engine2d_backend_lane_preferred_candidate(["cpu", "vulkan", "cuda"], false) equals `cuda`
   - Expected: engine2d_backend_lane_preferred_candidate(["cpu", "baremetal"], false) equals `cpu`
   - Expected: engine2d_backend_lane_preferred_candidate(["cpu", "baremetal"], true) equals `baremetal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("excludes explicit-native candidates from automatic selection")
# Positive control (include_explicit_native = true) proves the helper
# can still pick baremetal when the caller opts in, so the negative
# case below is a real exclusion and not a broken lookup.
expect(engine2d_backend_lane_preferred_candidate(["cpu", "vulkan", "cuda"], false)).to_equal("cuda")
expect(engine2d_backend_lane_preferred_candidate(["cpu", "baremetal"], false)).to_equal("cpu")
expect(engine2d_backend_lane_preferred_candidate(["cpu", "baremetal"], true)).to_equal("baremetal")
```

</details>

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

- `REQ-SSPEC-GPU`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2465e793ff4688b60c87a47fecd36e55887768e1b2cce69f2143d403e4f37ec6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2465e793ff4688b60c87a47fecd36e55887768e1b2cce69f2143d403e4f37ec6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2465e793ff4688b60c87a47fecd36e55887768e1b2cce69f2143d403e4f37ec6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/gpu/engine2d_backend_lane_order_parity_spec.spl
mirror: doc/06_spec/01_unit/gpu/engine2d_backend_lane_order_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/gpu/engine2d_backend_lane_order_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/gpu/engine2d_backend_lane_order_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/gpu/engine2d_backend_lane_order_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/gpu/engine2d_backend_lane_order_parity_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the full order explicit-native first and GPU-tier complete' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/engine2d_backend_lane_order_parity_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the drawing order native-first without explicit-native surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/engine2d_backend_lane_order_parity_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the summary a readable preference chain, not a joined list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
