# Backend Matrix Tauri Specification

> <details>

<!-- sdn-diagram:id=backend_matrix_tauri_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_matrix_tauri_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_matrix_tauri_spec -> std
backend_matrix_tauri_spec -> nogc_sync_mut
backend_matrix_tauri_spec -> common
backend_matrix_tauri_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_matrix_tauri_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Tauri Specification

## Scenarios

### GUI widget matrix tauri backend

<details>
<summary>Advanced: renders the widget matrix through the tauri backend</summary>

#### renders the widget matrix through the tauri backend

1. Err
   - Expected: e equals ``

2. Ok

3. Err
   - Expected: e equals ``

4. Ok
   - Expected: backend.backend_name() equals `tauri`
   - Expected: backend.supports_images() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/widget_matrix.ui.sdn")
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val backend_result = TauriBackend.new(4011)
        match backend_result:
            Err(e):
                expect(e).to_equal("")
            Ok(backend):
                expect(backend.backend_name()).to_equal("tauri")
                expect(backend.supports_images()).to_equal(true)
                val html = backend.render_html(state)
                expect(html).to_contain("widget-dropdown")
                expect(html).to_contain("widget-image")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_matrix_tauri_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI widget matrix tauri backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
