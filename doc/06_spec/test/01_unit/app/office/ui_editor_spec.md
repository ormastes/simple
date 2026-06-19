# ui_editor_spec

> Verifies the pure HTML UI design document substrate used by the Office suite to move toward a Figma-like editor surface while keeping SDD as the diagram interchange format.

<!-- sdn-diagram:id=ui_editor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_editor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_editor_spec -> std
ui_editor_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_editor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ui_editor_spec

Verifies the pure HTML UI design document substrate used by the Office suite to move toward a Figma-like editor surface while keeping SDD as the diagram interchange format.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/office_ui_editor.md |
| Plan | doc/03_plan/sys_test/office_ui_editor.md |
| Design | doc/05_design/app/office/office_ui_editor.md |
| Research | doc/01_research/local/office_ui_editor.md |
| Source | `test/01_unit/app/office/ui_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the pure HTML UI design document substrate used by the Office suite to
move toward a Figma-like editor surface while keeping SDD as the diagram
interchange format.

## Examples

`office_ui_design_parse` accepts simple positioned node records, renders a
stable HTML design canvas, serializes to `.sdd.sdn`-compatible node tables, and
guards edits with stale-label rejection.

**Requirements:** doc/02_requirements/feature/office_ui_editor.md
**Plan:** doc/03_plan/sys_test/office_ui_editor.md
**Design:** doc/05_design/app/office/office_ui_editor.md
**Research:** doc/01_research/local/office_ui_editor.md

## Scenarios

### Office UI editor substrate

#### names the HTML UI design document format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_ui_editor_format_name()).to_equal("HTML UI Design Document")
```

</details>

#### parses positioned frames and components

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val design = office_ui_design_parse("design: Login\nsize: 800x480\nnode frame|Login Card|frame|40|32|360|240|panel|base|container\nnode submit|Sign in|button|72|200|120|36|primary|controls|action")
expect(design.name).to_equal("Login")
expect(design.width).to_equal("800")
expect(design.height).to_equal("480")
expect(design.nodes.len()).to_equal(2)
expect(design.nodes[0].kind).to_equal("frame")
expect(design.nodes[1].component).to_equal("action")
```

</details>

#### renders inspector-ready positioned HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val design = office_ui_design_parse("design: Login\nsize: 800x480\nnode submit|Sign <in>|button|72|200|120|36|primary|controls|action")
val html = office_ui_design_render_html(design)
expect(html).to_contain("class=\"office-ui-design\"")
expect(html).to_contain("data-format=\"html-ui\"")
expect(html).to_contain("data-format-name=\"HTML UI Design Document\"")
expect(html).to_contain("data-id=\"submit\"")
expect(html).to_contain("data-layer=\"controls\"")
expect(html).to_contain("left: 72px")
expect(html).to_contain("Sign &lt;in&gt;")
```

</details>

#### serializes design nodes to SDD tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val design = office_ui_design_parse("design: Login\nnode card|Login Card|frame|40|32|360|240|panel|base|container\nnode submit|Sign in|button|72|200|120|36|primary|controls|action")
val sdd = office_ui_design_to_sdd(design)
expect(sdd).to_contain("graph: Login")
expect(sdd).to_contain("theme: office-ui")
expect(sdd).to_contain("nodes |id, label, css, role, shape, x, y, width, height, layer|")
expect(sdd).to_contain("card, \"Login Card\", panel, container, frame, 40, 32, 360, 240, base")
expect(sdd).to_contain("submit, \"Sign in\", primary, action, rounded, 72, 200, 120, 36, controls")
```

</details>

#### guards label updates with stale rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val design = office_ui_design_parse("design: Login\nnode submit|Sign in|button|72|200|120|36|primary|controls|action")
val accepted = office_ui_design_update_label_checked(design, "submit", "Sign in", "Continue")
expect(accepted.accepted).to_be(true)
expect(accepted.reason).to_equal("updated")
expect(accepted.design.nodes[0].label).to_equal("Continue")
val rejected = office_ui_design_update_label_checked(design, "submit", "Wrong", "Continue")
expect(rejected.accepted).to_be(false)
expect(rejected.reason).to_equal("stale-node")
expect(rejected.design.nodes[0].label).to_equal("Sign in")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/office_ui_editor.md](doc/02_requirements/feature/office_ui_editor.md)
- **Plan:** [doc/03_plan/sys_test/office_ui_editor.md](doc/03_plan/sys_test/office_ui_editor.md)
- **Design:** [doc/05_design/app/office/office_ui_editor.md](doc/05_design/app/office/office_ui_editor.md)
- **Research:** [doc/01_research/local/office_ui_editor.md](doc/01_research/local/office_ui_editor.md)


</details>
