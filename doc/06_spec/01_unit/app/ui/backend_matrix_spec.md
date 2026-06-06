# Backend Matrix Specification

> 1. Err

<!-- sdn-diagram:id=backend_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_matrix_spec -> std
backend_matrix_spec -> nogc_sync_mut
backend_matrix_spec -> common
backend_matrix_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Specification

## Scenarios

### GUI widget matrix parser

#### preserves layout aliases and widget props from SDN

1. Err
   - Expected: e equals ``

2. Ok
   - Expected: tree.title equals `Widget Matrix`
   - Expected: main != nil is true
   - Expected: main.layout equals `hbox`
   - Expected: progress != nil is true
   - Expected: progress.get_prop("value") equals `42`
   - Expected: checkbox != nil is true
   - Expected: checkbox.get_prop("checked") equals `true`
   - Expected: textfield != nil is true
   - Expected: textfield.get_prop("value") equals `alice`
   - Expected: textfield.get_prop("placeholder") equals `User name`
   - Expected: image != nil is true
   - Expected: image.get_prop("src") equals `/static/logo.png`
   - Expected: image.get_prop("alt") equals `Simple Logo`
   - Expected: tooltip != nil is true
   - Expected: tooltip.get_prop("target") equals `save_button`


<details>
<summary>Executable SPipe</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree(sample_ui)
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        expect(tree.title).to_equal("Widget Matrix")

        val main = tree.find_widget("main")
        expect(main != nil).to_equal(true)
        if main != nil:
            expect(main.layout).to_equal("hbox")

        val progress = tree.find_widget("progress")
        expect(progress != nil).to_equal(true)
        if progress != nil:
            expect(progress.get_prop("value")).to_equal("42")

        val checkbox = tree.find_widget("sync_checkbox")
        expect(checkbox != nil).to_equal(true)
        if checkbox != nil:
            expect(checkbox.get_prop("checked")).to_equal("true")

        val textfield = tree.find_widget("name_field")
        expect(textfield != nil).to_equal(true)
        if textfield != nil:
            expect(textfield.get_prop("value")).to_equal("alice")
            expect(textfield.get_prop("placeholder")).to_equal("User name")

        val image = tree.find_widget("logo")
        expect(image != nil).to_equal(true)
        if image != nil:
            expect(image.get_prop("src")).to_equal("/static/logo.png")
            expect(image.get_prop("alt")).to_equal("Simple Logo")

        val tooltip = tree.find_widget("help_tip")
        expect(tooltip != nil).to_equal(true)
        if tooltip != nil:
            expect(tooltip.get_prop("target")).to_equal("save_button")
```

</details>

### GUI widget matrix rendering

#### renders all widget families across shared renderers and backends

1. Err
   - Expected: e equals ``

2. Ok

3. var screen = Screen new

4. screen = render tui tree


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree(sample_ui)
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val st = state.tree
        val rn = st.root_node()
        val html = render_html_tree(rn, state)

        expect(html).to_contain("widget-menubar")
        expect(html).to_contain("widget-progress")
        expect(html).to_contain("widget-tabs")
        expect(html).to_contain("widget-list")
        expect(html).to_contain("widget-input")
        expect(html).to_contain("widget-textfield")
        expect(html).to_contain("widget-checkbox")
        expect(html).to_contain("widget-dropdown")
        expect(html).to_contain("widget-button")
        expect(html).to_contain("widget-divider")
        expect(html).to_contain("widget-table")
        expect(html).to_contain("widget-image")
        expect(html).to_contain("widget-tooltip")
        expect(html).to_contain("widget-dialog")
        expect(html).to_contain("Apply pending changes?")
        expect(html).to_contain("data-target=\"save_button\"")

        val st2 = state.tree
        val rn2 = st2.root_node()
        val rects = compute_layout(rn2, 0, 0, 480, 40)
        var screen = Screen.new(480, 40)
        val st3 = state.tree
        val rn3 = st3.root_node()
        screen = render_tui_tree(screen, rn3, rects, state)
        val output = screen.render()
        expect(output).to_contain("Widget coverage sample")
        expect(output).to_contain("42%")
        expect(output).to_contain("Overview")
        expect(output).to_contain("[x] Enable sync")
        expect(output).to_contain("[v] Auto")
        expect(output).to_contain("|alice|")
        expect(output).to_contain("[ Save ]")
        expect(output).to_contain("[IMG: Simple Logo]")
        expect(output).to_contain("Ready")
```

</details>

#### generates desktop and browser entries for the same sample app

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val web_src = generate_gui_entry(sample_ui, "web", 4020)
val tauri_src = generate_gui_entry(sample_ui, "tauri", 4021)
val electron_src = generate_gui_entry(sample_ui, "electron", 4022)
val tui_src = generate_gui_entry(sample_ui, "tui", 0)

expect(web_src).to_contain("run_web")
expect(tauri_src).to_contain("run_tauri")
expect(electron_src).to_contain("run_electron")
expect(tui_src).to_contain("ansi_enable_alt_screen")
expect(tui_src).to_contain("UI closed.")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI widget matrix parser
- GUI widget matrix rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
