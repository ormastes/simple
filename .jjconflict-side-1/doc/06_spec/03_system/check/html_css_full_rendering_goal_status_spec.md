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
- All 284 implemented Simple Web CSS properties are rendered in fixture CSS.
- The current full CSS inventory is tested as 394 properties, with 117 still
  unrendered and 117 held in unsupported-inventory ownership.
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

- Run the full rendering goal status check without network-dependent HTML fetches
   - Expected: code equals `0`
- Read the full rendering goal evidence
   - Expected: full_css_total equals `394`
   - Expected: full_css_rendered equals `277`
   - Expected: full_css_unrendered equals `117`
   - Expected: unsupported_inventory equals `117`
   - Expected: full_css_unrendered_properties.split(",").len() equals `117`
   - Expected: full_css_unrendered_properties does not contain `aspect-ratio`
   - Expected: full_css_unrendered_words does not contain `,accent-color,`
   - Expected: full_css_unrendered_words does not contain `,background-blend-mode,`
   - Expected: full_css_unrendered_words does not contain `,grid-column-gap,`
   - Expected: full_css_unrendered_words does not contain `,grid-gap,`
   - Expected: full_css_unrendered_words does not contain `,grid-row-gap,`
   - Expected: full_css_unrendered_words does not contain `,grid,`
   - Expected: full_css_unrendered_words does not contain `,grid-area,`
   - Expected: full_css_unrendered_words does not contain `,grid-auto-flow,`
   - Expected: full_css_unrendered_words does not contain `,grid-column,`
   - Expected: full_css_unrendered_words does not contain `,grid-column-start,`
   - Expected: full_css_unrendered_words does not contain `,grid-template,`
   - Expected: full_css_unrendered_words does not contain `,grid-template-columns,`
   - Expected: full_css_unrendered_words does not contain `,grid-template-rows,`
   - Expected: full_css_unrendered_words does not contain `,grid-row,`
   - Expected: full_css_unrendered_words does not contain `,grid-row-start,`
   - Expected: full_css_unrendered_words does not contain `,backface-visibility,`
   - Expected: full_css_unrendered_words does not contain `,border-collapse,`
   - Expected: full_css_unrendered_words does not contain `,border-spacing,`
   - Expected: full_css_unrendered_words does not contain `,caption-side,`
   - Expected: full_css_unrendered_words does not contain `,column-count,`
   - Expected: full_css_unrendered_words does not contain `,column-width,`
   - Expected: full_css_unrendered_words does not contain `,columns,`
   - Expected: full_css_unrendered_words does not contain `,column-rule,`
   - Expected: full_css_unrendered_words does not contain `,column-rule-color,`
   - Expected: full_css_unrendered_words does not contain `,list-style-image,`
   - Expected: full_css_unrendered_words does not contain `,justify-items,`
   - Expected: full_css_unrendered_words does not contain `,justify-self,`
   - Expected: full_css_unrendered_words does not contain `,text-emphasis,`
   - Expected: full_css_unrendered_words does not contain `,text-emphasis-color,`
   - Expected: full_css_unrendered_words does not contain `,text-emphasis-position,`
   - Expected: full_css_unrendered_words does not contain `,text-emphasis-style,`
   - Expected: full_css_unrendered_words does not contain `,list-style-position,`
   - Expected: full_css_unrendered_words does not contain `,column-rule-style,`
   - Expected: full_css_unrendered_words does not contain `,column-rule-width,`
   - Expected: full_css_unrendered_properties does not contain `object-fit`
   - Expected: full_css_unrendered_properties does not contain `object-position`
   - Expected: full_css_unrendered_words does not contain `,clip,`
   - Expected: full_css_unrendered_words does not contain `,clip-path,`
   - Expected: full_css_unrendered_words does not contain `,color-scheme,`
   - Expected: full_css_unrendered_words does not contain `,color-adjust,`
   - Expected: full_css_unrendered_words does not contain `,forced-color-adjust,`
   - Expected: full_css_unrendered_words does not contain `,print-color-adjust,`
   - Expected: full_css_unrendered_words does not contain `,orphans,`
   - Expected: full_css_unrendered_words does not contain `,widows,`
   - Expected: full_css_unrendered_words does not contain `,empty-cells,`
   - Expected: full_css_unrendered_words does not contain `,filter,`
   - Expected: full_css_unrendered_words does not contain `,place-content,`
   - Expected: full_css_unrendered_words does not contain `,place-items,`
   - Expected: full_css_unrendered_words does not contain `,place-self,`
   - Expected: full_css_unrendered_words does not contain `,rotate,`
   - Expected: full_css_unrendered_words does not contain `,scale,`
   - Expected: full_css_unrendered_words does not contain `,translate,`
   - Expected: full_css_unrendered_words does not contain `,background-attachment,`
   - Expected: full_css_unrendered_words does not contain `,margin-block,`
   - Expected: full_css_unrendered_words does not contain `,padding-block,`
   - Expected: full_css_unrendered_words does not contain `,block-size,`
   - Expected: full_css_unrendered_words does not contain `,inline-size,`
   - Expected: full_css_unrendered_words does not contain `,min-block-size,`
   - Expected: full_css_unrendered_words does not contain `,min-inline-size,`
   - Expected: full_css_unrendered_words does not contain `,max-block-size,`
   - Expected: full_css_unrendered_words does not contain `,max-inline-size,`
   - Expected: full_css_unrendered_words does not contain `,inset,`
   - Expected: full_css_unrendered_words does not contain `,inset-block,`
   - Expected: full_css_unrendered_words does not contain `,inset-block-start,`
   - Expected: full_css_unrendered_words does not contain `,inset-block-end,`
   - Expected: full_css_unrendered_words does not contain `,inset-inline,`
   - Expected: full_css_unrendered_words does not contain `,inset-inline-start,`
   - Expected: full_css_unrendered_words does not contain `,inset-inline-end,`
   - Expected: full_css_unrendered_words does not contain `,border-block,`
   - Expected: full_css_unrendered_words does not contain `,border-block-start,`
   - Expected: full_css_unrendered_words does not contain `,border-block-end,`
   - Expected: full_css_unrendered_words does not contain `,border-inline,`
   - Expected: full_css_unrendered_words does not contain `,border-inline-start,`
   - Expected: full_css_unrendered_words does not contain `,border-inline-end,`
   - Expected: full_css_unrendered_words does not contain `,clear,`
   - Expected: full_css_unrendered_words does not contain `,content,`
   - Expected: full_css_unrendered_words does not contain `,content-visibility,`
   - Expected: full_css_unrendered_words does not contain `,contain,`
   - Expected: full_css_unrendered_words does not contain `,float,`
   - Expected: full_css_unrendered_words does not contain `,font-family,`
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
   - Expected: full_css_unrendered_words does not contain `,font-kerning,`
   - Expected: full_css_unrendered_words does not contain `,font-optical-sizing,`
- expect not
- expect not
- expect not
- expect not
   - Expected: full_css_unrendered_words does not contain `,font-synthesis,`
- expect not
- expect not
- expect not
   - Expected: full_css_unrendered_words does not contain `,font-synthesis-weight,`
   - Expected: full_css_unrendered_words does not contain `,image-rendering,`
   - Expected: full_css_unrendered_words does not contain `,line-break,`
   - Expected: full_css_unrendered_words does not contain `,hyphens,`
   - Expected: full_css_unrendered_words does not contain `,text-align-all,`
   - Expected: full_css_unrendered_words does not contain `,text-justify,`
   - Expected: full_css_unrendered_words does not contain `,writing-mode,`
   - Expected: full_css_unrendered_words does not contain `,text-combine-upright,`
   - Expected: full_css_unrendered_words does not contain `,text-orientation,`
   - Expected: full_css_unrendered_words does not contain `,list-style,`
   - Expected: full_css_unrendered_words does not contain `,list-style-type,`
   - Expected: full_css_unrendered_words does not contain `,scrollbar-color,`
   - Expected: full_css_unrendered_words does not contain `,scrollbar-width,`
   - Expected: full_css_unrendered_words does not contain `,table-layout,`
   - Expected: full_css_unrendered_words does not contain `,vertical-align,`
   - Expected: full_css_unrendered_words does not contain `,quotes,`
   - Expected: animation_css_unrendered_properties equals ``
   - Expected: full_css_unrendered_properties does not contain `accent-color`
   - Expected: full_css_unrendered_words does not contain `,grid-template-areas,`
   - Expected: full_css_unrendered_words does not contain `,will-change,`
- Verify the operator report names the full CSS gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 191 lines folded for reproduction.
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
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_total_count=284")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_rendered_count=284")
expect(evidence).to_contain("html_css_full_rendering_goal_implemented_css_missing=")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_all_css_properties_ready_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_all_css_properties_ready_reason=full-css-rendering-incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_required_min_count=390")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_rendered_count=277")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_unrendered_properties=")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_status=pass")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_scope=animation-transition-transform-css")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_total_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_rendered_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_unrendered_count=0")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_unrendered_properties=")
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
expect(full_css_rendered).to_equal("277")
expect(full_css_unrendered).to_equal("117")
expect(unsupported_inventory).to_equal("117")
expect(full_css_unrendered_properties.split(",").len()).to_equal(117)
expect(full_css_unrendered_properties.contains("aspect-ratio")).to_equal(false)
expect(full_css_unrendered_words.contains(",accent-color,")).to_equal(false)
expect(full_css_unrendered_words.contains(",background-blend-mode,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-column-gap,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-gap,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-row-gap,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-area,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-auto-flow,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-column,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-column-start,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-template,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-template-columns,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-template-rows,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-row,")).to_equal(false)
expect(full_css_unrendered_words.contains(",grid-row-start,")).to_equal(false)
expect(full_css_unrendered_words.contains(",backface-visibility,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-collapse,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-spacing,")).to_equal(false)
expect(full_css_unrendered_words.contains(",caption-side,")).to_equal(false)
expect(full_css_unrendered_words.contains(",column-count,")).to_equal(false)
expect(full_css_unrendered_words.contains(",column-width,")).to_equal(false)
expect(full_css_unrendered_words.contains(",columns,")).to_equal(false)
expect(full_css_unrendered_words.contains(",column-rule,")).to_equal(false)
expect(full_css_unrendered_words.contains(",column-rule-color,")).to_equal(false)
expect(full_css_unrendered_words.contains(",list-style-image,")).to_equal(false)
expect(full_css_unrendered_words.contains(",justify-items,")).to_equal(false)
expect(full_css_unrendered_words.contains(",justify-self,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-emphasis,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-emphasis-color,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-emphasis-position,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-emphasis-style,")).to_equal(false)
expect(full_css_unrendered_words.contains(",list-style-position,")).to_equal(false)
expect(full_css_unrendered_words.contains(",column-rule-style,")).to_equal(false)
expect(full_css_unrendered_words.contains(",column-rule-width,")).to_equal(false)
expect(full_css_unrendered_properties.contains("object-fit")).to_equal(false)
expect(full_css_unrendered_properties.contains("object-position")).to_equal(false)
expect(full_css_unrendered_words.contains(",clip,")).to_equal(false)
expect(full_css_unrendered_words.contains(",clip-path,")).to_equal(false)
expect(full_css_unrendered_words.contains(",color-scheme,")).to_equal(false)
expect(full_css_unrendered_words.contains(",color-adjust,")).to_equal(false)
expect(full_css_unrendered_words.contains(",forced-color-adjust,")).to_equal(false)
expect(full_css_unrendered_words.contains(",print-color-adjust,")).to_equal(false)
expect(full_css_unrendered_words.contains(",orphans,")).to_equal(false)
expect(full_css_unrendered_words.contains(",widows,")).to_equal(false)
expect(full_css_unrendered_words.contains(",empty-cells,")).to_equal(false)
expect(full_css_unrendered_words.contains(",filter,")).to_equal(false)
expect(full_css_unrendered_words.contains(",place-content,")).to_equal(false)
expect(full_css_unrendered_words.contains(",place-items,")).to_equal(false)
expect(full_css_unrendered_words.contains(",place-self,")).to_equal(false)
expect(full_css_unrendered_words.contains(",rotate,")).to_equal(false)
expect(full_css_unrendered_words.contains(",scale,")).to_equal(false)
expect(full_css_unrendered_words.contains(",translate,")).to_equal(false)
expect(full_css_unrendered_words.contains(",background-attachment,")).to_equal(false)
expect(full_css_unrendered_words.contains(",margin-block,")).to_equal(false)
expect(full_css_unrendered_words.contains(",padding-block,")).to_equal(false)
expect(full_css_unrendered_words.contains(",block-size,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inline-size,")).to_equal(false)
expect(full_css_unrendered_words.contains(",min-block-size,")).to_equal(false)
expect(full_css_unrendered_words.contains(",min-inline-size,")).to_equal(false)
expect(full_css_unrendered_words.contains(",max-block-size,")).to_equal(false)
expect(full_css_unrendered_words.contains(",max-inline-size,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset-block,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset-block-start,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset-block-end,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset-inline,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset-inline-start,")).to_equal(false)
expect(full_css_unrendered_words.contains(",inset-inline-end,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-block,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-block-start,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-block-end,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-inline,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-inline-start,")).to_equal(false)
expect(full_css_unrendered_words.contains(",border-inline-end,")).to_equal(false)
expect(full_css_unrendered_words.contains(",clear,")).to_equal(false)
expect(full_css_unrendered_words.contains(",content,")).to_equal(false)
expect(full_css_unrendered_words.contains(",content-visibility,")).to_equal(false)
expect(full_css_unrendered_words.contains(",contain,")).to_equal(false)
expect(full_css_unrendered_words.contains(",float,")).to_equal(false)
expect(full_css_unrendered_words.contains(",font-family,")).to_equal(false)
expect_not(full_css_unrendered_words.contains(",font-feature-settings,"))
expect_not(full_css_unrendered_words.contains(",font-language-override,"))
expect_not(full_css_unrendered_words.contains(",font-variation-settings,"))
expect_not(full_css_unrendered_words.contains(",font-variant,"))
expect_not(full_css_unrendered_words.contains(",font-variant-caps,"))
expect_not(full_css_unrendered_words.contains(",font-variant-alternates,"))
expect_not(full_css_unrendered_words.contains(",font-variant-east-asian,"))
expect_not(full_css_unrendered_words.contains(",font-variant-emoji,"))
expect_not(full_css_unrendered_words.contains(",font-variant-ligatures,"))
expect_not(full_css_unrendered_words.contains(",font-variant-numeric,"))
expect_not(full_css_unrendered_words.contains(",font-variant-position,"))
expect(full_css_unrendered_words.contains(",font-kerning,")).to_equal(false)
expect(full_css_unrendered_words.contains(",font-optical-sizing,")).to_equal(false)
expect_not(full_css_unrendered_words.contains(",font-palette,"))
expect_not(full_css_unrendered_words.contains(",font-stretch,"))
expect_not(full_css_unrendered_words.contains(",font-width,"))
expect_not(full_css_unrendered_words.contains(",font-size-adjust,"))
expect(full_css_unrendered_words.contains(",font-synthesis,")).to_equal(false)
expect_not(full_css_unrendered_words.contains(",font-synthesis-small-caps,"))
expect_not(full_css_unrendered_words.contains(",font-synthesis-position,"))
expect_not(full_css_unrendered_words.contains(",font-synthesis-style,"))
expect(full_css_unrendered_words.contains(",font-synthesis-weight,")).to_equal(false)
expect(full_css_unrendered_words.contains(",image-rendering,")).to_equal(false)
expect(full_css_unrendered_words.contains(",line-break,")).to_equal(false)
expect(full_css_unrendered_words.contains(",hyphens,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-align-all,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-justify,")).to_equal(false)
expect(full_css_unrendered_words.contains(",writing-mode,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-combine-upright,")).to_equal(false)
expect(full_css_unrendered_words.contains(",text-orientation,")).to_equal(false)
expect(full_css_unrendered_words.contains(",list-style,")).to_equal(false)
expect(full_css_unrendered_words.contains(",list-style-type,")).to_equal(false)
expect(full_css_unrendered_words.contains(",scrollbar-color,")).to_equal(false)
expect(full_css_unrendered_words.contains(",scrollbar-width,")).to_equal(false)
expect(full_css_unrendered_words.contains(",table-layout,")).to_equal(false)
expect(full_css_unrendered_words.contains(",vertical-align,")).to_equal(false)
expect(full_css_unrendered_words.contains(",quotes,")).to_equal(false)
expect(animation_css_unrendered_properties).to_equal("")
expect(full_css_unrendered_properties.contains("accent-color")).to_equal(false)
expect(full_css_unrendered_properties).to_contain("border-image-source")
expect(full_css_unrendered_words.contains(",grid-template-areas,")).to_equal(false)
expect(full_css_unrendered_properties).to_contain("scroll-padding-inline-start")
expect(full_css_unrendered_properties).to_contain("view-transition-name")
expect(full_css_unrendered_words.contains(",will-change,")).to_equal(false)

step("Verify the operator report names the full CSS gap")
val report = file_read("build/test-html-css-full-rendering-goal-status/report.md")
expect(report).to_contain("# HTML/CSS Full Rendering Goal Status")
expect(report).to_contain("- status: incomplete")
expect(report).to_contain("- all HTML elements ready: pass")
expect(report).to_contain("- implemented CSS ready: pass")
expect(report).to_contain("- full CSS inventory ready: incomplete")
expect(report).to_contain("- HTML tags rendered: 105/105")
expect(report).to_contain("- implemented CSS rendered: 284/284")
expect(report).to_contain("- full CSS unrendered:")
expect(report).to_contain("- animation CSS rendered: 0/0 (pass)")
```

</details>

#### fails in strict mode while the full CSS inventory is not rendered

- Run the same gate in strict mode
   - Expected: code equals `1`
- Assert strict mode still emits inspectable evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the same gate in strict mode")
val command = "rm -rf build/test-html-css-full-rendering-goal-status-strict && BUILD_DIR=build/test-html-css-full-rendering-goal-status-strict REPORT_PATH=build/test-html-css-full-rendering-goal-status-strict/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 sh scripts/check/check-html-css-full-rendering-goal-status.shs --strict"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

step("Assert strict mode still emits inspectable evidence")
val evidence = stdout
expect(evidence).to_contain("html_css_full_rendering_goal_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_full_css_status=incomplete")
expect(evidence).to_contain("html_css_full_rendering_goal_animation_css_status=pass")
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
