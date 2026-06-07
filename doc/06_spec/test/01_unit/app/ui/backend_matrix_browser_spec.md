# Backend Matrix Browser Specification

> 1. Err

<!-- sdn-diagram:id=backend_matrix_browser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_matrix_browser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_matrix_browser_spec -> std
backend_matrix_browser_spec -> nogc_sync_mut
backend_matrix_browser_spec -> common
backend_matrix_browser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_matrix_browser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Browser Specification

## Scenarios

### GUI widget matrix browser backend

#### renders through the shared web API without a document shell

1. Err
   - Expected: e equals ``

2. Ok

3. Err
   - Expected: e equals ``

4. Ok
   - Expected: html contains `widget-button`
   - Expected: html contains `widget-statusbar`
   - Expected: html does not contain `<html>`
   - Expected: backend.web_render_target equals `pure_simple`
   - Expected: backend.viewport_width() equals `64`
   - Expected: backend.viewport_height() equals `48`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/widget_matrix.ui.sdn")
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val backend_result = BrowserBackend.create(64, 48, "software")
        match backend_result:
            Err(e):
                expect(e).to_equal("")
            Ok(backend):
                val html = backend.render_html(state)
                expect(html.contains("widget-button")).to_equal(true)
                expect(html.contains("widget-statusbar")).to_equal(true)
                expect(html.contains("<html>")).to_equal(false)
                expect(backend.web_render_target).to_equal("pure_simple")
                expect(backend.viewport_width()).to_equal(64)
                expect(backend.viewport_height()).to_equal(48)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_matrix_browser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI widget matrix browser backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
