# Backend Matrix Web Specification

> <details>

<!-- sdn-diagram:id=backend_matrix_web_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_matrix_web_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_matrix_web_spec -> std
backend_matrix_web_spec -> nogc_sync_mut
backend_matrix_web_spec -> common
backend_matrix_web_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_matrix_web_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Web Specification

## Scenarios

### GUI widget matrix web backend

<details>
<summary>Advanced: renders the widget matrix through the web backend</summary>

#### renders the widget matrix through the web backend

1. Err
   - Expected: e equals ``

2. Ok
   - Expected: backend.backend_name() equals `web`
   - Expected: backend.supports_mouse() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/widget_matrix.ui.sdn")
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val backend = WebBackend.new(4010)
        expect(backend.backend_name()).to_equal("web")
        expect(backend.supports_mouse()).to_equal(true)
        val html = backend.render_html(state)
        expect(html).to_contain("widget-dialog")
        expect(html).to_contain("widget-tooltip")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_matrix_web_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI widget matrix web backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
