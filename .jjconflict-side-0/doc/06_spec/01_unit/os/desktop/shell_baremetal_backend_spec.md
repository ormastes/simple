# Shell Baremetal Backend Specification

> 1. var backend =  capture backend

<!-- sdn-diagram:id=shell_baremetal_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_baremetal_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_baremetal_backend_spec -> std
shell_baremetal_backend_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_baremetal_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Baremetal Backend Specification

## Scenarios

### baremetal desktop overlay backend contract

#### draws through CompositorBackend instead of requiring raw Engine2D

1. var backend =  capture backend
   - Expected: backend.fill_count > 0 is true
   - Expected: backend.text_count > 0 is true
   - Expected: backend.present_count equals `0`
   - Expected: backend.last_text equals `12:34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = _capture_backend()
_draw_baremetal_overlay(
    backend,
    ["Editor"],
    ["7501 Editor running"],
    0,
    800,
    600,
    "12:34"
)

expect(backend.fill_count > 0).to_equal(true)
expect(backend.text_count > 0).to_equal(true)
expect(backend.present_count).to_equal(0)
expect(backend.last_text).to_equal("12:34")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_baremetal_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- baremetal desktop overlay backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
