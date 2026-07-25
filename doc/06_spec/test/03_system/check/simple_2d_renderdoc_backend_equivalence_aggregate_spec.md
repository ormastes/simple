# Simple 2d Renderdoc Backend Equivalence Aggregate Specification

> <details>

<!-- sdn-diagram:id=simple_2d_renderdoc_backend_equivalence_aggregate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_2d_renderdoc_backend_equivalence_aggregate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_2d_renderdoc_backend_equivalence_aggregate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_2d_renderdoc_backend_equivalence_aggregate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2d Renderdoc Backend Equivalence Aggregate Specification

## Scenarios

### Backend equivalence aggregate

#### should report focused and intensive Linux evidence with timing and RSS

- Run the focused profile once
   - Exec capture: after_step
- Run the intensive profile after focused evidence passes
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: ["elapsed_ms", "max_rss_kb", "blocker_count"].len() equals `3`
- pending equivalence aggregate
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the focused profile once")
step("Run the intensive profile after focused evidence passes")
expect(["elapsed_ms", "max_rss_kb", "blocker_count"].len()).to_equal(3)
pending_equivalence_aggregate()
```

</details>

#### should include QEMU guest SIMD and board-capability rows

- Collect x86 AArch64 RV64 and physical-board checkpoints
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: ["x86_64", "aarch64", "rv64", "physical-board"].len() equals `4`
- pending equivalence aggregate
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Collect x86 AArch64 RV64 and physical-board checkpoints")
expect(["x86_64", "aarch64", "rv64", "physical-board"].len()).to_equal(4)
pending_equivalence_aggregate()
```

</details>

<details>
<summary>Advanced: should keep qualification externally incomplete without native hosts</summary>

#### should keep qualification externally incomplete without native hosts

- Evaluate native Windows macOS and physical-board rows
   - Expected: "incomplete_external" equals `incomplete_external`
- pending equivalence aggregate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate native Windows macOS and physical-board rows")
expect("incomplete_external").to_equal("incomplete_external")
pending_equivalence_aggregate()
```

</details>


</details>

<details>
<summary>Advanced: should expose every stable blocker and requirement identifier</summary>

#### should expose every stable blocker and requirement identifier

- Inspect blocker and traceability collections
- pending equivalence aggregate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect blocker and traceability collections")
expect("REQ-021").to_start_with("REQ-")
pending_equivalence_aggregate()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend equivalence aggregate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
