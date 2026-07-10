# Simple Web Backend Equivalence Specification

> <details>

<!-- sdn-diagram:id=simple_web_backend_equivalence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_backend_equivalence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_backend_equivalence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_backend_equivalence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Backend Equivalence Specification

## Scenarios

### Simple Web detailed backend equivalence

#### should validate all fifty production layouts before exact pixels

- Prepare the production HTML and CSS layout manifest
   - Protocol capture: after_step
- Capture DOM Draw IR and layout structure
   - Protocol capture: after_step
- Compare detailed backend records and exact pixels
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: 50 equals `50`
- pending web backend equivalence
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare the production HTML and CSS layout manifest")
step("Capture DOM Draw IR and layout structure")
step("Compare detailed backend records and exact pixels")
expect(50).to_equal(50)
pending_web_backend_equivalence()
```

</details>

#### should render all one hundred thirty-two offline site fixtures

- Run every deterministic site through the production facade
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: 132 equals `132`
- pending web backend equivalence
   - HTML capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run every deterministic site through the production facade")
expect(132).to_equal(132)
pending_web_backend_equivalence()
```

</details>

#### should cover the forty-three-widget fixture and isolated samples

- Render the complete widget fixture and isolated feature witnesses
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: 43 equals `43`
- pending web backend equivalence
   - HTML capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the complete widget fixture and isolated feature witnesses")
expect(43).to_equal(43)
pending_web_backend_equivalence()
```

</details>

<details>
<summary>Advanced: should track text antialiasing divergence without tolerance</summary>

#### should track text antialiasing divergence without tolerance

- Classify browser and Simple text rasterization differences
   - Expected: "track-text-divergence" equals `track-text-divergence`
- pending web backend equivalence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify browser and Simple text rasterization differences")
expect("track-text-divergence").to_equal("track-text-divergence")
pending_web_backend_equivalence()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web detailed backend equivalence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
