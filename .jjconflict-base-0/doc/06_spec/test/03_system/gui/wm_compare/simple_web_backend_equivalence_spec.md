# Simple Web Backend Equivalence Specification

> <details>

<!-- sdn-diagram:id=simple_web_backend_equivalence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_backend_equivalence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_backend_equivalence_spec -> std
simple_web_backend_equivalence_spec -> app
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

#### validates fifty production layouts with exact pixels

- Render the first fifty deterministic production layouts
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: first_production_layouts_match(50, 40, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the first fifty deterministic production layouts")
expect(first_production_layouts_match(50, 40, 30)).to_equal(true)
```

</details>

#### renders all one hundred thirty-two offline site fixtures

- Run every deterministic site through the production facade
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: all_offline_site_fixtures_match(40, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run every deterministic site through the production facade")
expect(all_offline_site_fixtures_match(40, 30)).to_equal(true)
```

</details>

#### covers the forty-three widget fixture witnesses

- Derive and verify the complete widget inventory
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: widget_coverage_gate_passes() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive and verify the complete widget inventory")
expect(widget_coverage_gate_passes()).to_equal(true)
```

</details>

#### keeps text-bearing software and cpu layout pixels exact

- Compare production layout output without a tolerance
   - Expected: comparison.different_pixels equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare production layout output without a tolerance")
val sample = build_famous_site_sample_corpus()[0]
val software = simple_web_layout_render_html_pixels(sample.html, 160, 120, "software")
val cpu = simple_web_layout_render_html_pixels(sample.html, 160, 120, "cpu")
val comparison = compare_exact(software, cpu, 160, 120)
expect(comparison.different_pixels).to_equal(0)
```

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
