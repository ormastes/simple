# HTML/CSS full rendering goal status gate

> Validates the non-launching status gate for the full HTML/CSS rendering objective. The current renderer must prove all WHATWG HTML tags and the implemented Simple Web CSS subset through real rendered fixtures, while the broader W3C CSS inventory remains explicitly incomplete until those properties move from inventory assignment into rendered behavior.

<!-- sdn-diagram:id=html_css_full_rendering_goal_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_css_full_rendering_goal_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_css_full_rendering_goal_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_css_full_rendering_goal_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML/CSS full rendering goal status gate

Validates the non-launching status gate for the full HTML/CSS rendering objective. The current renderer must prove all WHATWG HTML tags and the implemented Simple Web CSS subset through real rendered fixtures, while the broader W3C CSS inventory remains explicitly incomplete until those properties move from inventory assignment into rendered behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/html_css_full_rendering_goal_status_spec.spl` |
| Updated | 2026-06-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the non-launching status gate for the full HTML/CSS rendering
objective. The current renderer must prove all WHATWG HTML tags and the
implemented Simple Web CSS subset through real rendered fixtures, while the
broader W3C CSS inventory remains explicitly incomplete until those properties
move from inventory assignment into rendered behavior.

**Plan:** N/A
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-html-css-full-rendering-goal-status \
REPORT_PATH=build/test-html-css-full-rendering-goal-status/report.md \
HTML_CSS_RENDERING_MANIFEST_FETCH=0 \
sh scripts/check/check-html-css-full-rendering-goal-status.shs
```

## Acceptance

- All 105 HTML tags are rendered in the 50-case fixture manifest.
- All 240 implemented Simple Web CSS properties are rendered in fixture CSS.
- The current full CSS inventory is tested as 394 properties, with 161 still
  unrendered and 161 held in unsupported-inventory ownership.
- Animation, transition, and transform CSS are reported separately; the current
  implemented subset renders those properties, so that sub-goal is `pass`.
- Readiness keys explicitly distinguish all HTML elements, the implemented CSS
  subset, and the full CSS inventory so operators cannot mistake subset
  coverage for all CSS properties being ready.
- The full W3C CSS rendering goal reports `incomplete` while unsupported CSS
  properties remain only inventory-assigned.
- Strict mode fails closed until the full CSS inventory is rendered.

## Scenarios

### HTML/CSS full rendering goal status gate

#### reports complete HTML and implemented CSS while full CSS remains incomplete

- Read the full rendering goal evidence fixture from the latest wrapper run
   - Expected: full_css_total equals `394`
   - Expected: full_css_rendered equals `233`
   - Expected: full_css_unrendered equals `161`
   - Expected: unsupported_inventory equals `161`
   - Expected: full_css_unrendered_properties.split(",").len() equals `161`
   - Expected: animation_css_unrendered_properties equals ``
- Verify the wrapper source still writes the operator report rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the full rendering goal evidence fixture from the latest wrapper run")
val evidence = file_read("test/fixtures/html_css/full_rendering_goal_status_color_scheme.env")
expect(evidence).to_contain("html_css_full_rendering_goal_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_reason=full-css-rendering-incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_ready_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_ready_reason=full-css-rendering-incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_sspec_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_rendering_manifest_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_all_html_elements_ready_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_all_html_elements_ready_reason=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_total_count=105")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_required_count=105")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_rendered_count=105")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_missing=")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_all_implemented_css_ready_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_all_implemented_css_ready_reason=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_scope=implemented-simple-web-css")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_total_count=240")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_rendered_count=240")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_missing=")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_all_css_properties_ready_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_all_css_properties_ready_reason=full-css-rendering-incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_required_min_count=390")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_rendered_count=233")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_unrendered_properties=")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_scope=animation-transition-transform-css")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_total_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_rendered_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_unrendered_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_unrendered_properties=")
expect(evidence).to_contain("accent-color")
expect(evidence).to_contain("grid-template-columns")
expect(evidence).to_contain("background-blend-mode")
expect(evidence).to_contain("html_css_full_rendering_goal_manifest_case_count=50")
expect(evidence).to_contain("html_css_full_rendering_goal_manifest_required_case_count=50")

val full_css_total = _value_of(evidence, "html_css_full_rendering_goal_full_css_total_count")
val full_css_rendered = _value_of(evidence, "html_css_full_rendering_goal_full_css_rendered_count")
val full_css_unrendered = _value_of(evidence, "html_css_full_rendering_goal_full_css_unrendered_count")
val full_css_unrendered_properties = _value_of(evidence, "html_css_full_rendering_goal_full_css_unrendered_properties")
val full_css_unrendered_words = "," + full_css_unrendered_properties + ","
val animation_css_unrendered_properties = _value_of(evidence, "html_css_full_rendering_goal_animation_css_unrendered_properties")
val unsupported_inventory = _value_of(evidence, "html_css_full_rendering_goal_unsupported_css_inventory_count")
expect(full_css_total).to_equal("394")
expect(full_css_rendered).to_equal("233")
expect(full_css_unrendered).to_equal("161")
expect(unsupported_inventory).to_equal("161")
expect(full_css_unrendered_properties.split(",").len()).to_equal(161)
expect(animation_css_unrendered_properties).to_equal("")
expect(full_css_unrendered_properties).to_contain("accent-color")
expect(full_css_unrendered_properties).to_contain("border-image-source")
expect(full_css_unrendered_properties).to_contain("grid-template-columns")
expect(full_css_unrendered_properties).to_contain("scroll-padding-inline-start")
expect(full_css_unrendered_properties).to_contain("view-transition-name")

step("Verify the wrapper source still writes the operator report rows")
val script = file_read("scripts/check/check-html-css-full-rendering-goal-status.shs")
expect(script).to_contain("echo \"# HTML/CSS Full Rendering Goal Status\"")
expect(script).to_contain("echo \"- implemented CSS rendered: $render_css_covered/$implemented_total ($render_css_scope)\"")
expect(script).to_contain("echo \"- full CSS unrendered: $unrendered_css_count\"")
expect(script).to_contain("echo \"- animation CSS rendered: $((animation_css_total - animation_css_unrendered))/$animation_css_total ($animation_css_status)\"")
```

</details>

#### keeps strict mode fail-closed while the full CSS inventory is not rendered

- Inspect the wrapper strict-mode contract without rerunning the full evidence pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the wrapper strict-mode contract without rerunning the full evidence pipeline")
val script = file_read("scripts/check/check-html-css-full-rendering-goal-status.shs")
expect(script).to_contain("STRICT=0")
expect(script).to_contain("--strict)")
expect(script).to_contain("STRICT=1")
expect(script).to_contain("if [ \"$STRICT\" = \"1\" ]; then")
expect(script).to_contain("exit 1")
expect(script).to_contain("if [ \"$status\" = \"incomplete\" ]; then")
expect(script).to_contain("exit 0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
