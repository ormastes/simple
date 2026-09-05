# Backend Matrix Browser Specification

> <details>

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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Browser Specification

## Scenarios

### GUI widget matrix browser backend

#### renders through the shared web API without a document shell

- Err
   - Expected: e equals ``
- Ok
- Err
   - Expected: e equals ``
- Ok
   - Expected: html contains `widget-button`
   - Expected: html contains `widget-statusbar`
   - Expected: html does not contain `<html>`
   - Expected: backend.web_render_target equals `pure_simple`
   - Expected: backend.viewport_width() equals `64`
   - Expected: backend.viewport_height() equals `48`


<details>
<summary>Executable SSpec</summary>

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

#### keeps canonical Engine2D backend selection visible through the browser adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BrowserBackend.create(64, 48, "cuda").unwrap().gpu_backend()).to_equal("cuda")
expect(BrowserBackend.create(64, 48, "hip").unwrap().gpu_backend()).to_equal("rocm")
expect(BrowserBackend.create(64, 48, "opencl").unwrap().gpu_backend()).to_equal("opencl")
expect(BrowserBackend.create(64, 48, "vulkan").unwrap().gpu_backend()).to_equal("vulkan")
expect(BrowserBackend.create(64, 48, "simd_cpu").unwrap().gpu_backend()).to_equal("cpu_simd")
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
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
