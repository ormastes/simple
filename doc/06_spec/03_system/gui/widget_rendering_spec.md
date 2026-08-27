# Widget Rendering Contract

> This system spec verifies the headless HTML rendering contract for parsed UI SDN widgets. It covers demo, minimal, browser-backend, and layout-container paths without requiring the parallel GUI framework implementation lane.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders demo.ui.sdn to HTML
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo.ui.sdn to HTML")
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

- contains widget CSS classes
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains widget CSS classes")
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

- renders minimal.ui.sdn to HTML
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders minimal.ui.sdn to HTML")
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

- paints parsed SDN content into the framebuffer
   - Expected: backend.framebuffer.pixel_at(1, 1) equals `0xE0E0E0`
   - Expected: e equals ``
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("paints parsed SDN content into the framebuffer")
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

- produces layout classes
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces layout classes")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7ea5c9ff63a9a780a12b2e29439a56b03b4badaf5ed8947f2a6366ae640ac45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7ea5c9ff63a9a780a12b2e29439a56b03b4badaf5ed8947f2a6366ae640ac45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7ea5c9ff63a9a780a12b2e29439a56b03b4badaf5ed8947f2a6366ae640ac45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/widget_rendering_spec.spl
mirror: doc/06_spec/03_system/gui/widget_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/widget_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/widget_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/widget_rendering_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders demo.ui.sdn to HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/widget_rendering_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains widget CSS classes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/widget_rendering_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders minimal.ui.sdn to HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
