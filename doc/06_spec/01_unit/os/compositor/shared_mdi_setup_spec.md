# Shared Mdi Setup Specification

> <details>

<!-- sdn-diagram:id=shared_mdi_setup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_mdi_setup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_mdi_setup_spec -> std
shared_mdi_setup_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_mdi_setup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Mdi Setup Specification

## Scenarios

### shared MDI setup

#### defines the canonical five Simple Web app surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surfaces = shared_mdi_surfaces()
expect(surfaces.len()).to_equal(5)
expect(surfaces[0].title).to_equal("Terminal")
expect(surfaces[0].app_id).to_equal("terminal")
expect(surfaces[1].title).to_equal("Editor")
expect(surfaces[1].app_id).to_equal("editor")
expect(surfaces[2].title).to_equal("Browser")
expect(surfaces[2].app_id).to_equal("browser")
expect(surfaces[3].title).to_equal("File Manager")
expect(surfaces[3].app_id).to_equal("file-manager")
expect(surfaces[4].title).to_equal("Calculator")
expect(surfaces[4].app_id).to_equal("calculator")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/shared_mdi_setup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared MDI setup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
