# Backend Matrix Specification

> Tests covering GUI widget matrix parser, GUI widget matrix rendering, GUI backend matrix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Specification

## Scenarios

### GUI widget matrix parser

#### preserves layout aliases and widget props from SDN

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves layout aliases and widget props from SDN
   - Expected: e equals ``
   - Expected: tree.title equals `Widget Matrix`
   - Expected: main.layout equals `hbox`
   - Expected: progress.get_prop("value") equals `42`
   - Expected: checkbox.get_prop("checked") equals `true`
   - Expected: textfield.get_prop("value") equals `alice`
   - Expected: textfield.get_prop("placeholder") equals `User name`
   - Expected: image.get_prop("src") equals `/static/logo.png`
   - Expected: image.get_prop("alt") equals `Simple Logo`
   - Expected: tooltip.get_prop("target") equals `save_button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves layout aliases and widget props from SDN")
val tree_result = parse_ui_to_tree(sample_ui)
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        expect(tree.title).to_equal("Widget Matrix")

        val main = tree.find_widget("main")
        assert_not_equal(main, nil)
        if main != nil:
            expect(main.layout).to_equal("hbox")

        val progress = tree.find_widget("progress")
        assert_not_equal(progress, nil)
        if progress != nil:
            expect(progress.get_prop("value")).to_equal("42")

        val checkbox = tree.find_widget("sync_checkbox")
        assert_not_equal(checkbox, nil)
        if checkbox != nil:
            expect(checkbox.get_prop("checked")).to_equal("true")

        val textfield = tree.find_widget("name_field")
        assert_not_equal(textfield, nil)
        if textfield != nil:
            expect(textfield.get_prop("value")).to_equal("alice")
            expect(textfield.get_prop("placeholder")).to_equal("User name")

        val image = tree.find_widget("logo")
        assert_not_equal(image, nil)
        if image != nil:
            expect(image.get_prop("src")).to_equal("/static/logo.png")
            expect(image.get_prop("alt")).to_equal("Simple Logo")

        val tooltip = tree.find_widget("help_tip")
        assert_not_equal(tooltip, nil)
        if tooltip != nil:
            expect(tooltip.get_prop("target")).to_equal("save_button")
```

</details>

### GUI widget matrix rendering

#### renders all widget families into shared HTML

- renders all widget families into shared HTML
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders all widget families into shared HTML")
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
```

</details>

#### renders all interactive widget markers into TUI output

- renders all interactive widget markers into TUI output
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders all interactive widget markers into TUI output")
val tree_result = parse_ui_to_tree(sample_ui)
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val st2 = state.tree
        val rn2 = st2.root_node()
        val rects = compute_layout(rn2, 0, 0, 140, 40)
        var screen = Screen.new(140, 40)
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

### GUI backend matrix

<details>
<summary>Advanced: web backend renders the widget matrix</summary>

#### web backend renders the widget matrix

- web backend renders the widget matrix
   - Expected: e equals ``
   - Expected: backend.backend_name() equals `web`
   - Expected: backend.supports_mouse() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("web backend renders the widget matrix")
val tree_result = parse_ui_to_tree(sample_ui)
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

<details>
<summary>Advanced: tauri backend renders the widget matrix</summary>

#### tauri backend renders the widget matrix

- tauri backend renders the widget matrix
   - Expected: e equals ``
   - Expected: e equals ``
   - Expected: backend.backend_name() equals `tauri`
   - Expected: backend.supports_images() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tauri backend renders the widget matrix")
val tree_result = parse_ui_to_tree(sample_ui)
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

<details>
<summary>Advanced: electron backend renders the widget matrix</summary>

#### electron backend renders the widget matrix

- electron backend renders the widget matrix
   - Expected: e equals ``
   - Expected: e equals ``
   - Expected: backend.backend_name() equals `electron`
   - Expected: backend.supports_color() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("electron backend renders the widget matrix")
val tree_result = parse_ui_to_tree(sample_ui)
match tree_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tree):
        val state = init_state(tree)
        val backend_result = ElectronBackend.new(4012)
        match backend_result:
            Err(e):
                expect(e).to_equal("")
            Ok(backend):
                expect(backend.backend_name()).to_equal("electron")
                expect(backend.supports_color()).to_equal(true)
                val html = backend.render_html(state)
                expect(html).to_contain("widget-button")
                expect(html).to_contain("widget-statusbar")
```

</details>


</details>

#### pure simple browser backend renders through the shared web API

- pure simple browser backend renders through the shared web API
   - Expected: e equals ``
   - Expected: e equals ``
   - Expected: backend.web_render_target equals `pure_simple`
   - Expected: backend.last_artifact_pixels equals `64 * 48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pure simple browser backend renders through the shared web API")
val tree_result = parse_ui_to_tree(sample_ui)
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
                expect(html).to_contain("widget-button")
                expect(html).to_contain("widget-statusbar")
                expect(html).not_to_contain("<html>")
                backend.render_frame(state.tree, state)
                expect(backend.web_render_target).to_equal("pure_simple")
                expect(backend.last_artifact_capabilities).to_contain("touch")
                expect(backend.last_artifact_html).to_contain("<div id=\"app\">")
                expect(backend.last_artifact_pixels).to_equal(64 * 48)
```

</details>

#### generates desktop and browser entries for the same sample app

- generates desktop and browser entries for the same sample app


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates desktop and browser entries for the same sample app")
val web_src = generate_gui_entry(sample_ui, "web", 4020)
val tauri_src = generate_gui_entry(sample_ui, "tauri", 4021)
val electron_src = generate_gui_entry(sample_ui, "electron", 4022)
val tui_src = generate_gui_entry(sample_ui, "tui", 0)

expect(web_src).to_contain("run_web")
expect(tauri_src).to_contain("run_tauri")
expect(electron_src).to_contain("run_electron")
expect(tui_src).to_contain("run_standalone_tui")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/backend_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI widget matrix parser, GUI widget matrix rendering, GUI backend matrix.
- GUI widget matrix parser
- GUI widget matrix rendering
- GUI backend matrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25d8820dde3e7a633fdcf9a808126d58f2499a2dfda2dae6dd5dae115dab3347`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25d8820dde3e7a633fdcf9a808126d58f2499a2dfda2dae6dd5dae115dab3347`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25d8820dde3e7a633fdcf9a808126d58f2499a2dfda2dae6dd5dae115dab3347`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/backend_matrix_spec.spl
mirror: doc/06_spec/unit/app/ui/backend_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/backend_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/backend_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/backend_matrix_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves layout aliases and widget props from SDN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/backend_matrix_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders all widget families into shared HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/backend_matrix_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders all interactive widget markers into TUI output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
