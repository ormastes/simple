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
| Updated | 2026-06-01 |
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
- All 66 implemented Simple Web CSS properties are rendered in fixture CSS.
- The current full CSS inventory is tested as 394 properties, with 328 still
  unrendered and 335 held in unsupported-inventory ownership.
- Animation, transition, and transform CSS are reported as a separate
  incomplete sub-goal until those properties have rendered fixture coverage.
- The full W3C CSS rendering goal reports `incomplete` while unsupported CSS
  properties remain only inventory-assigned.
- Strict mode fails closed until the full CSS inventory is rendered.

## Scenarios

### HTML/CSS full rendering goal status gate

#### reports complete HTML and implemented CSS while full CSS remains incomplete

- Run the full rendering goal status check without network-dependent HTML fetches
   - Expected: code equals `0`
- Read the full rendering goal evidence
   - Expected: full_css_total equals `394`
   - Expected: full_css_rendered equals `66`
   - Expected: full_css_unrendered equals `328`
   - Expected: unsupported_inventory equals `335`
   - Expected: full_css_unrendered_properties.split(",").len() equals `328`
   - Expected: animation_css_unrendered_properties.split(",").len() equals `18`
- Verify the operator report names the full CSS gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the full rendering goal status check without network-dependent HTML fetches")
val command = "rm -rf build/test-html-css-full-rendering-goal-status && BUILD_DIR=build/test-html-css-full-rendering-goal-status REPORT_PATH=build/test-html-css-full-rendering-goal-status/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 sh scripts/check/check-html-css-full-rendering-goal-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read the full rendering goal evidence")
val evidence = file_read("build/test-html-css-full-rendering-goal-status/evidence.env")
expect(evidence).to_contain("html_css_full_rendering_goal_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_reason=full-css-rendering-incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_sspec_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_rendering_manifest_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_total_count=105")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_required_count=105")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_rendered_count=105")
expect(evidence).to_contain("html_css_full_rendering_goal_html_tag_missing=")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_scope=implemented-simple-web-css")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_total_count=66")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_rendered_count=66")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_missing=")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_required_min_count=390")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_rendered_count=66")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_unrendered_properties=")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_scope=animation-transition-transform-css")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_total_count=18")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_rendered_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_unrendered_count=18")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_unrendered_properties=")
expect(evidence).to_contain("animation-duration")
expect(evidence).to_contain("transition-property")
expect(evidence).to_contain("transform-origin")
expect(evidence).to_contain("accent-color")
expect(evidence).to_contain("grid-template-columns")
expect(evidence).to_contain("writing-mode")
expect(evidence).to_contain("html_css_full_rendering_goal_manifest_case_count=50")
expect(evidence).to_contain("html_css_full_rendering_goal_manifest_required_case_count=50")

val full_css_total = _value_of(evidence, "html_css_full_rendering_goal_full_css_total_count")
val full_css_rendered = _value_of(evidence, "html_css_full_rendering_goal_full_css_rendered_count")
val full_css_unrendered = _value_of(evidence, "html_css_full_rendering_goal_full_css_unrendered_count")
val full_css_unrendered_properties = _value_of(evidence, "html_css_full_rendering_goal_full_css_unrendered_properties")
val animation_css_unrendered_properties = _value_of(evidence, "html_css_full_rendering_goal_animation_css_unrendered_properties")
val unsupported_inventory = _value_of(evidence, "html_css_full_rendering_goal_unsupported_css_inventory_count")
expect(full_css_total).to_equal("394")
expect(full_css_rendered).to_equal("66")
expect(full_css_unrendered).to_equal("328")
expect(unsupported_inventory).to_equal("335")
expect(full_css_unrendered_properties.split(",").len()).to_equal(328)
expect(animation_css_unrendered_properties.split(",").len()).to_equal(18)
expect(full_css_unrendered_properties).to_contain("accent-color")
expect(full_css_unrendered_properties).to_contain("border-image-source")
expect(full_css_unrendered_properties).to_contain("grid-template-columns")
expect(full_css_unrendered_properties).to_contain("scroll-padding-inline-start")
expect(full_css_unrendered_properties).to_contain("view-transition-name")
expect(full_css_unrendered_properties).to_contain("writing-mode")

step("Verify the operator report names the full CSS gap")
val report = file_read("build/test-html-css-full-rendering-goal-status/report.md")
expect(report).to_contain("# HTML/CSS Full Rendering Goal Status")
expect(report).to_contain("- status: incomplete")
expect(report).to_contain("- HTML tags rendered: 105/105")
expect(report).to_contain("- implemented CSS rendered: 66/66")
expect(report).to_contain("- full CSS unrendered:")
expect(report).to_contain("- animation CSS rendered: 0/18 (incomplete)")
```

</details>

#### fails in strict mode while the full CSS inventory is not rendered

- Run the same gate in strict mode
   - Expected: code equals `1`
- Assert strict mode still writes inspectable evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the same gate in strict mode")
val command = "rm -rf build/test-html-css-full-rendering-goal-status-strict && BUILD_DIR=build/test-html-css-full-rendering-goal-status-strict REPORT_PATH=build/test-html-css-full-rendering-goal-status-strict/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 sh scripts/check/check-html-css-full-rendering-goal-status.shs --strict"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

step("Assert strict mode still writes inspectable evidence")
val evidence = file_read("build/test-html-css-full-rendering-goal-status-strict/evidence.env")
expect(evidence).to_contain("html_css_full_rendering_goal_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_unrendered_count=")
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
