# Widget Rendering Contract

> This system spec verifies the headless HTML rendering contract for parsed UI SDN widgets. It covers demo, minimal, browser-backend, and layout-container paths without requiring the parallel GUI framework implementation lane.

<!-- sdn-diagram:id=widget_rendering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_rendering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_rendering_spec -> std
widget_rendering_spec -> nogc_sync_mut
widget_rendering_spec -> common
widget_rendering_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_rendering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Rendering Contract

This system spec verifies the headless HTML rendering contract for parsed UI SDN widgets. It covers demo, minimal, browser-backend, and layout-container paths without requiring the parallel GUI framework implementation lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/widget_rendering_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the headless HTML rendering contract for parsed UI
SDN widgets. It covers demo, minimal, browser-backend, and layout-container
paths without requiring the parallel GUI framework implementation lane.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Syntax

Each scenario parses a UI SDN fixture, initializes UI state, renders HTML or a
software framebuffer, and asserts concrete rendered content.

## Examples

- `demo.ui.sdn` renders to nontrivial HTML with widget classes.
- `minimal.ui.sdn` renders nonempty HTML.
- `hello_gui.ui.sdn` paints a known background pixel through BrowserBackend.

## Scenarios

### Widget HTML Rendering — Demo UI

<details>
<summary>Advanced: renders demo.ui.sdn to HTML</summary>

#### renders demo.ui.sdn to HTML _(slow)_

1. Ok

2. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = init_state(tree)
        val html = render_html_tree(state.tree.root, state)
        expect(html.len()).to_be_greater_than(50)
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: contains widget CSS classes</summary>

#### contains widget CSS classes _(slow)_

1. Ok

2. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = init_state(tree)
        val html = render_html_tree(state.tree.root, state)
        # HTML should contain widget type classes
        expect(html).to_contain("widget-")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

### Widget HTML Rendering — Minimal UI

<details>
<summary>Advanced: renders minimal.ui.sdn to HTML</summary>

#### renders minimal.ui.sdn to HTML _(slow)_

1. Ok

2. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = init_state(tree)
        val html = render_html_tree(state.tree.root, state)
        expect(html.len()).to_be_greater_than(0)
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

### Browser Backend Rendering — Hello GUI

<details>
<summary>Advanced: paints parsed SDN content into the framebuffer</summary>

#### paints parsed SDN content into the framebuffer _(slow)_

1. Ok

2. Ok

3. backend render frame
   - Expected: backend.framebuffer.pixel_at(1, 1) equals `0xE0E0E0`

4. backend shutdown

5. Err
   - Expected: e equals ``

6. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/hello_gui.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = UIState.new(tree)
        val backend_result = BrowserBackend.create(96, 64, "software")
        match backend_result:
            Ok(backend) :
                backend.render_frame(tree, state)
                expect(backend.framebuffer.pixel_at(1, 1)).to_equal(0xE0E0E0)
                backend.shutdown()
            Err(e) :
                expect(e).to_equal("")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

### Widget HTML Rendering — Layout Containers

<details>
<summary>Advanced: produces layout classes</summary>

#### produces layout classes _(slow)_

1. Ok

2. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = init_state(tree)
        val html = render_html_tree(state.tree.root, state)
        # Layout types should produce CSS classes
        expect(html).to_contain("layout-")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
