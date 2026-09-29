# Backend Lane Font Offload Candidate Specification

> Tests covering nogc Engine2D font-offload candidate selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Lane Font Offload Candidate Specification

## Scenarios

### nogc Engine2D font-offload candidate selection

#### selects qualcomm, which the gc mirror also tiers for font offload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects qualcomm, which the gc mirror also tiers for font offload


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects qualcomm, which the gc mirror also tiers for font offload")
assert_equal(engine2d_backend_lane_preferred_font_offload_candidate(["qualcomm"]), "qualcomm")
```

</details>

#### selects intel, which the gc mirror also tiers for font offload

- selects intel, which the gc mirror also tiers for font offload


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects intel, which the gc mirror also tiers for font offload")
assert_equal(engine2d_backend_lane_preferred_font_offload_candidate(["intel"]), "intel")
```

</details>

#### prefers the higher-tier backend when several candidates are offered

- prefers the higher-tier backend when several candidates are offered


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers the higher-tier backend when several candidates are offered")
assert_equal(
    engine2d_backend_lane_preferred_font_offload_candidate(["cpu", "qualcomm", "cuda"]),
    "cuda"
)
```

</details>

#### drops a backend that is not in the font-offload order at all

- drops a backend that is not in the font-offload order at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops a backend that is not in the font-offload order at all")
assert_equal(engine2d_backend_lane_preferred_font_offload_candidate(["nvidia"]), "")
```

</details>

#### drops nothing silently: every name in the declared order is selectable

- drops nothing silently: every name in the declared order is selectable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops nothing silently: every name in the declared order is selectable")
for backend in engine2d_font_offload_backend_order():
    assert_equal(engine2d_backend_lane_preferred_font_offload_candidate([backend]), backend)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc Engine2D font-offload candidate selection.
- nogc Engine2D font-offload candidate selection

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aad21d4c8a065ee24141a3caf5ad781babdfe621cb627d89962e51c76965dfa9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aad21d4c8a065ee24141a3caf5ad781babdfe621cb627d89962e51c76965dfa9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aad21d4c8a065ee24141a3caf5ad781babdfe621cb627d89962e51c76965dfa9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects qualcomm, which the gc mirror also tiers for font offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects intel, which the gc mirror also tiers for font offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/backend_lane_font_offload_candidate_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers the higher-tier backend when several candidates are offered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
