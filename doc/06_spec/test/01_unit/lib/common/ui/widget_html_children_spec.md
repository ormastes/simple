# Widget Html Children Specification

> <details>

<!-- sdn-diagram:id=widget_html_children_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_html_children_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_html_children_spec -> std
widget_html_children_spec -> common
widget_html_children_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_html_children_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Html Children Specification

## Scenarios

### common ui builder children render to html

#### preserves child ids and widget kinds in children()

- Build a column with text, image, and button children
- Read child nodes back through the public child list API
   - Expected: children.len() equals `3`
   - Expected: children[0].id equals `children_kind_text`
   - Expected: children[0].kind_name() equals `text`
   - Expected: children[1].id equals `children_kind_image`
   - Expected: children[1].kind_name() equals `image`
   - Expected: children[2].id equals `children_kind_button`
   - Expected: children[2].kind_name() equals `button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a column with text, image, and button children")
val hero = label("children_kind_text", "Text")
val preview = image("children_kind_image", "data:image/svg+xml,%3Csvg%3E%3C/svg%3E", "Preview")
val action = button("children_kind_button", "Run", "run_children_kind")
val root = column("children_kind_root", [hero, preview, action])
val children = root.children()

step("Read child nodes back through the public child list API")
expect(children.len()).to_equal(3)
expect(children[0].id).to_equal("children_kind_text")
expect(children[0].kind_name()).to_equal("text")
expect(children[1].id).to_equal("children_kind_image")
expect(children[1].kind_name()).to_equal("image")
expect(children[2].id).to_equal("children_kind_button")
expect(children[2].kind_name()).to_equal("button")
```

</details>

#### renders generated widget leaves instead of empty panels

- Render a builder tree through the HTML widget renderer
- Assert leaf widgets are visible in the HTML output


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a builder tree through the HTML widget renderer")
val html = sample_html()

step("Assert leaf widgets are visible in the HTML output")
expect(html).to_contain("id=\"html_child_text\"")
expect(html).to_contain("class=\"widget-text")
expect(html).to_contain("AB CD")
expect(html).to_contain("id=\"html_child_image\"")
expect(html).to_contain("class=\"widget-image")
expect(html).to_contain("id=\"html_child_button\"")
expect(html).to_contain("class=\"widget-button")
expect(html).to_contain("data-action=\"run_html_child\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_html_children_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- common ui builder children render to html

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
