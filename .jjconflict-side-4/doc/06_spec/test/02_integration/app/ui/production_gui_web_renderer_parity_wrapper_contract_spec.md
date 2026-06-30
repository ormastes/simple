# Production Gui Web Renderer Parity Wrapper Contract Specification

> <details>

<!-- sdn-diagram:id=production_gui_web_renderer_parity_wrapper_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_renderer_parity_wrapper_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_renderer_parity_wrapper_contract_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_renderer_parity_wrapper_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Gui Web Renderer Parity Wrapper Contract Specification

## Scenarios

### production GUI web renderer parity wrapper contract

#### forwards fresh layout-manifest mode by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = run_wrapper_with_resume("")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=pass")
expect(evidence).to_contain("layout_layout_resume_seen=0")
```

</details>

#### forwards layout-manifest resume only through the production override

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = run_wrapper_with_resume("1")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=pass")
expect(evidence).to_contain("layout_layout_resume_seen=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/ui/production_gui_web_renderer_parity_wrapper_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- production GUI web renderer parity wrapper contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
