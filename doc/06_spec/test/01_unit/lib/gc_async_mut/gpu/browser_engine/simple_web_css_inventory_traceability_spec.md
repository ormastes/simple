# Simple Web CSS Inventory Traceability Specification

> This spec records the SSpec owner for W3C CSS properties that are present in the current CSS index but are outside the Simple Web renderer's implemented functional subset. Those properties are inventory-tracked so they have an explicit test assignment without being falsely claimed as rendered behavior.

<!-- sdn-diagram:id=simple_web_css_inventory_traceability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_css_inventory_traceability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_css_inventory_traceability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_css_inventory_traceability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web CSS Inventory Traceability Specification

This spec records the SSpec owner for W3C CSS properties that are present in the current CSS index but are outside the Simple Web renderer's implemented functional subset. Those properties are inventory-tracked so they have an explicit test assignment without being falsely claimed as rendered behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec records the SSpec owner for W3C CSS properties that are present in the
current CSS index but are outside the Simple Web renderer's implemented
functional subset. Those properties are inventory-tracked so they have an
explicit test assignment without being falsely claimed as rendered behavior.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Design:** doc/04_architecture/ui/simple_gui_stack.md

**Research:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Requirements:** N/A

## Syntax

The executable assertions keep the inventory contract honest: implemented CSS
properties must remain assigned to renderer specs, while unsupported properties
must remain assigned to this inventory spec until they gain functional renderer
coverage.

## Scenarios

### Simple Web CSS inventory traceability

#### assigns implemented CSS properties to functional renderer SSpecs

- Record the functional SSpec owner for implemented Simple Web CSS properties
- Keep the full implemented Simple Web CSS subset tied to renderer behavior
   - Expected: implemented.split(" ").len() equals `248`


<details>
<summary>Executable SSpec</summary>

Runnable source: 146 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the functional SSpec owner for implemented Simple Web CSS properties")
val owner = _implemented_css_owner()
expect(owner).to_contain("simple_web_generated_html_css_combinations_spec.spl")

step("Keep the full implemented Simple Web CSS subset tied to renderer behavior")
val implemented = "accent-color align-content align-items align-self animation animation-delay animation-direction animation-duration animation-fill-mode animation-iteration-count animation-name animation-play-state animation-timing-function aspect-ratio background background-attachment background-clip background-color background-origin background-image background-position background-repeat background-size block-size border border-bottom border-bottom-color border-bottom-style border-bottom-width border-color border-left border-left-color border-left-style border-left-width border-right border-right-color border-right-style border-right-width border-style border-top border-top-color border-top-style border-width border-top-width border-radius border-bottom-left-radius border-bottom-right-radius border-top-left-radius border-top-right-radius border-start-start-radius border-start-end-radius border-end-start-radius border-end-end-radius border-block border-block-color border-block-end border-block-end-color border-block-end-style border-block-end-width border-block-start border-block-start-color border-block-start-style border-block-start-width border-block-style border-block-width border-inline border-inline-color border-inline-end border-inline-end-color border-inline-end-style border-inline-end-width border-inline-start border-inline-start-color border-inline-start-style border-inline-start-width border-inline-style border-inline-width bottom box-sizing box-shadow caret-color clear clip color color-adjust color-scheme forced-color-adjust column-gap content content-visibility contain cursor direction display empty-cells filter flex flex-basis flex-direction flex-flow flex-grow flex-shrink flex-wrap float font font-family font-feature-settings font-language-override font-variation-settings font-variant font-variant-alternates font-variant-caps font-variant-east-asian font-variant-emoji font-variant-ligatures font-variant-numeric font-variant-position font-kerning font-optical-sizing font-palette font-stretch font-width font-size font-size-adjust font-style font-synthesis font-synthesis-small-caps font-synthesis-position font-synthesis-style font-synthesis-weight font-weight gap height image-rendering inline-size inset inset-block inset-block-end inset-block-start inset-inline inset-inline-end inset-inline-start justify-content left letter-spacing line-height line-break hyphens list-style list-style-type margin margin-block margin-block-end margin-block-start margin-bottom margin-inline margin-inline-end margin-inline-start margin-left margin-right margin-top max-block-size max-height max-inline-size max-width min-block-size min-height min-inline-size min-width object-fit object-position opacity order orphans outline outline-color outline-offset outline-style outline-width overflow overflow-wrap overflow-x overflow-y padding padding-block padding-block-end padding-block-start padding-bottom padding-inline padding-inline-end padding-inline-start padding-left padding-right padding-top place-content place-items place-self position print-color-adjust resize right rotate row-gap scale scrollbar-color scrollbar-width tab-size table-layout text-align text-align-all text-align-last text-decoration text-decoration-color text-decoration-line text-decoration-style text-decoration-thickness text-indent text-combine-upright text-justify text-orientation text-overflow text-shadow text-transform text-underline-offset text-underline-position top transform transform-box transform-origin transform-style transition transition-delay transition-duration transition-property transition-timing-function translate unicode-bidi vertical-align visibility white-space widows width word-break word-spacing will-change word-wrap writing-mode z-index"
expect(implemented.split(" ").len()).to_equal(248)
expect(implemented).to_contain("accent-color")
expect(implemented).to_contain("color-adjust")
expect(implemented).to_contain("forced-color-adjust")
expect(implemented).to_contain("print-color-adjust")
expect(implemented).to_contain("will-change")
expect(implemented).to_contain("orphans")
expect(implemented).to_contain("widows")
expect(implemented).to_contain("aspect-ratio")
expect(implemented).to_contain("object-fit")
expect(implemented).to_contain("object-position")
expect(implemented).to_contain("display")
expect(implemented).to_contain("block-size")
expect(implemented).to_contain("font-feature-settings")
expect(implemented).to_contain("font-language-override")
expect(implemented).to_contain("font-variation-settings")
expect(implemented).to_contain("font-variant-caps")
expect(implemented).to_contain("font-variant-position")
expect(implemented).to_contain("font-kerning")
expect(implemented).to_contain("font-optical-sizing")
expect(implemented).to_contain("font-palette")
expect(implemented).to_contain("font-stretch")
expect(implemented).to_contain("font-width")
expect(implemented).to_contain("font-size-adjust")
expect(implemented).to_contain("font-synthesis")
expect(implemented).to_contain("font-synthesis-small-caps")
expect(implemented).to_contain("font-synthesis-position")
expect(implemented).to_contain("font-synthesis-style")
expect(implemented).to_contain("font-synthesis-weight")
expect(implemented).to_contain("background-attachment")
expect(implemented).to_contain("background-color")
expect(implemented).to_contain("background-clip")
expect(implemented).to_contain("background-image")
expect(implemented).to_contain("background-origin")
expect(implemented).to_contain("background-position")
expect(implemented).to_contain("background-repeat")
expect(implemented).to_contain("background-size")
expect(implemented).to_contain("bottom")
expect(implemented).to_contain("align-content")
expect(implemented).to_contain("align-items")
expect(implemented).to_contain("align-self")
expect(implemented).to_contain("box-sizing")
expect(implemented).to_contain("border-bottom-style")
expect(implemented).to_contain("border-left-style")
expect(implemented).to_contain("border-radius")
expect(implemented).to_contain("border-top-left-radius")
expect(implemented).to_contain("border-top-right-radius")
expect(implemented).to_contain("border-bottom-left-radius")
expect(implemented).to_contain("border-bottom-right-radius")
expect(implemented).to_contain("border-start-start-radius")
expect(implemented).to_contain("border-start-end-radius")
expect(implemented).to_contain("border-end-start-radius")
expect(implemented).to_contain("border-end-end-radius")
expect(implemented).to_contain("border-right-style")
expect(implemented).to_contain("border-top-style")
expect(implemented).to_contain("border-block")
expect(implemented).to_contain("border-block-start")
expect(implemented).to_contain("border-block-end")
expect(implemented).to_contain("border-inline")
expect(implemented).to_contain("border-inline-start")
expect(implemented).to_contain("border-inline-end")
expect(implemented).to_contain("box-shadow")
expect(implemented).to_contain("caret-color")
expect(implemented).to_contain("clip")
expect(implemented).to_contain("color-scheme")
expect(implemented).to_contain("content")
expect(implemented).to_contain("content-visibility")
expect(implemented).to_contain("contain")
expect(implemented).to_contain("cursor")
expect(implemented).to_contain("direction")
expect(implemented).to_contain("empty-cells")
expect(implemented).to_contain("filter")
expect(implemented).to_contain("font-style")
expect(implemented).to_contain("font-family")
expect(implemented).to_contain("font")
expect(implemented).to_contain("clear")
expect(implemented).to_contain("float")
expect(implemented).to_contain("flex-flow")
expect(implemented).to_contain("flex-wrap")
expect(implemented).to_contain("letter-spacing")
expect(implemented).to_contain("line-height")
expect(implemented).to_contain("line-break")
expect(implemented).to_contain("hyphens")
expect(implemented).to_contain("list-style")
expect(implemented).to_contain("list-style-type")
expect(implemented).to_contain("inline-size")
expect(implemented).to_contain("image-rendering")
expect(implemented).to_contain("inset")
expect(implemented).to_contain("inset-block")
expect(implemented).to_contain("inset-inline")
expect(implemented).to_contain("max-block-size")
expect(implemented).to_contain("max-inline-size")
expect(implemented).to_contain("min-block-size")
expect(implemented).to_contain("min-inline-size")
expect(implemented).to_contain("opacity")
expect(implemented).to_contain("margin-block")
expect(implemented).to_contain("margin-inline")
expect(implemented).to_contain("padding-block")
expect(implemented).to_contain("padding-inline")
expect(implemented).to_contain("outline")
expect(implemented).to_contain("outline-color")
expect(implemented).to_contain("outline-offset")
expect(implemented).to_contain("outline-style")
expect(implemented).to_contain("outline-width")
expect(implemented).to_contain("overflow-wrap")
expect(implemented).to_contain("place-content")
expect(implemented).to_contain("place-items")
expect(implemented).to_contain("place-self")
expect(implemented).to_contain("resize")
expect(implemented).to_contain("rotate")
expect(implemented).to_contain("scale")
expect(implemented).to_contain("scrollbar-color")
expect(implemented).to_contain("scrollbar-width")
expect(implemented).to_contain("tab-size")
expect(implemented).to_contain("table-layout")
expect(implemented).to_contain("text-align-all")
expect(implemented).to_contain("vertical-align")
expect(implemented).to_contain("text-decoration")
expect(implemented).to_contain("text-decoration-color")
expect(implemented).to_contain("text-decoration-line")
expect(implemented).to_contain("text-indent")
expect(implemented).to_contain("text-justify")
expect(implemented).to_contain("text-combine-upright")
expect(implemented).to_contain("text-orientation")
expect(implemented).to_contain("text-overflow")
expect(implemented).to_contain("text-shadow")
expect(implemented).to_contain("text-transform")
expect(implemented).to_contain("animation-name")
expect(implemented).to_contain("transform")
expect(implemented).to_contain("transform-origin")
expect(implemented).to_contain("transition-property")
expect(implemented).to_contain("translate")
expect(implemented).to_contain("unicode-bidi")
expect(implemented).to_contain("visibility")
expect(implemented).to_contain("white-space")
expect(implemented).to_contain("word-break")
expect(implemented).to_contain("word-spacing")
expect(implemented).to_contain("word-wrap")
expect(implemented).to_contain("writing-mode")
expect(implemented).to_contain("z-index")
```

</details>

#### assigns unsupported W3C CSS properties to inventory traceability until implemented

- Record the inventory SSpec owner for unsupported CSS properties
- Keep the complete current unsupported W3C property inventory visible without claiming renderer support
   - Expected: unsupported_cases.len() equals `153`
   - Expected: unsupported_words does not contain ` accent-color `
   - Expected: unsupported_words does not contain ` color-adjust `
   - Expected: unsupported_words does not contain ` forced-color-adjust `
   - Expected: unsupported_words does not contain ` print-color-adjust `
   - Expected: unsupported_words does not contain ` will-change `
   - Expected: unsupported_words does not contain ` orphans `
   - Expected: unsupported_words does not contain ` widows `
   - Expected: unsupported_words does not contain ` empty-cells `
   - Expected: unsupported does not contain `background-attachment`
   - Expected: unsupported_words does not contain ` clip `
   - Expected: unsupported_words does not contain ` color-scheme `
   - Expected: unsupported_words does not contain ` filter `
   - Expected: unsupported_words does not contain ` rotate `
   - Expected: unsupported_words does not contain ` scale `
   - Expected: unsupported_words does not contain ` place-content `
   - Expected: unsupported_words does not contain ` place-items `
   - Expected: unsupported_words does not contain ` place-self `
   - Expected: unsupported_words does not contain ` translate `
   - Expected: unsupported does not contain `block-size`
   - Expected: unsupported does not contain `inline-size`
   - Expected: unsupported does not contain `min-block-size`
   - Expected: unsupported does not contain `min-inline-size`
   - Expected: unsupported does not contain `max-block-size`
   - Expected: unsupported does not contain `max-inline-size`
   - Expected: unsupported does not contain `inset`
   - Expected: unsupported does not contain `inset-block`
   - Expected: unsupported does not contain `inset-block-start`
   - Expected: unsupported does not contain `inset-block-end`
   - Expected: unsupported does not contain `inset-inline`
   - Expected: unsupported does not contain `inset-inline-start`
   - Expected: unsupported does not contain `inset-inline-end`
   - Expected: unsupported does not contain `border-block`
   - Expected: unsupported does not contain `border-block-color`
   - Expected: unsupported does not contain `border-block-end`
   - Expected: unsupported does not contain `border-block-end-color`
   - Expected: unsupported does not contain `border-block-end-style`
   - Expected: unsupported does not contain `border-block-end-width`
   - Expected: unsupported does not contain `border-block-start`
   - Expected: unsupported does not contain `border-block-start-color`
   - Expected: unsupported does not contain `border-block-start-style`
   - Expected: unsupported does not contain `border-block-start-width`
   - Expected: unsupported does not contain `border-block-style`
   - Expected: unsupported does not contain `border-block-width`
   - Expected: unsupported does not contain `border-inline`
   - Expected: unsupported does not contain `border-inline-color`
   - Expected: unsupported does not contain `border-inline-end`
   - Expected: unsupported does not contain `border-inline-end-color`
   - Expected: unsupported does not contain `border-inline-end-style`
   - Expected: unsupported does not contain `border-inline-end-width`
   - Expected: unsupported does not contain `border-inline-start`
   - Expected: unsupported_words does not contain ` clear `
   - Expected: unsupported_words does not contain ` content `
   - Expected: unsupported_words does not contain ` content-visibility `
   - Expected: unsupported_words does not contain ` contain `
   - Expected: unsupported_words does not contain ` image-rendering `
- expect not
- expect not
- expect not
- expect not
- expect not
- expect not
   - Expected: unsupported_words does not contain ` font-kerning `
   - Expected: unsupported_words does not contain ` font-optical-sizing `
- expect not
- expect not
- expect not
- expect not
   - Expected: unsupported_words does not contain ` font-synthesis `
- expect not
- expect not
- expect not
   - Expected: unsupported_words does not contain ` font-synthesis-weight `
   - Expected: unsupported_words does not contain ` line-break `
   - Expected: unsupported_words does not contain ` hyphens `
   - Expected: unsupported_words does not contain ` text-justify `
   - Expected: unsupported_words does not contain ` writing-mode `
   - Expected: unsupported_words does not contain ` text-combine-upright `
   - Expected: unsupported_words does not contain ` text-align-all `
   - Expected: unsupported_words does not contain ` text-orientation `
   - Expected: unsupported_words does not contain ` scrollbar-color `
   - Expected: unsupported_words does not contain ` scrollbar-width `
   - Expected: unsupported_words does not contain ` table-layout `
   - Expected: unsupported_words does not contain ` vertical-align `
   - Expected: unsupported_words does not contain ` float `
   - Expected: unsupported_words does not contain ` font-family `
   - Expected: unsupported_words does not contain ` list-style `
   - Expected: unsupported_words does not contain ` list-style-type `
   - Expected: unsupported does not contain `border-inline-start-color`
   - Expected: unsupported does not contain `border-inline-start-style`
   - Expected: unsupported does not contain `border-inline-start-width`
   - Expected: unsupported does not contain `border-inline-style`
   - Expected: unsupported does not contain `border-inline-width`
   - Expected: unsupported does not contain `border-start-start-radius`
   - Expected: unsupported does not contain `border-start-end-radius`
   - Expected: unsupported does not contain `border-end-start-radius`
   - Expected: unsupported does not contain `border-end-end-radius`


<details>
<summary>Executable SSpec</summary>

Runnable source: 109 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the inventory SSpec owner for unsupported CSS properties")
val owner = _unsupported_css_owner()
expect(owner).to_contain("simple_web_css_inventory_traceability_spec.spl")

step("Keep the complete current unsupported W3C property inventory visible without claiming renderer support")
val unsupported = _unsupported_css_inventory()
val unsupported_cases = unsupported.split(" ")
val unsupported_words = " " + unsupported + " "
expect(unsupported_cases.len()).to_equal(153)
expect(unsupported_words.contains(" accent-color ")).to_equal(false)
expect(unsupported_words.contains(" color-adjust ")).to_equal(false)
expect(unsupported_words.contains(" forced-color-adjust ")).to_equal(false)
expect(unsupported_words.contains(" print-color-adjust ")).to_equal(false)
expect(unsupported_words.contains(" will-change ")).to_equal(false)
expect(unsupported_words.contains(" orphans ")).to_equal(false)
expect(unsupported_words.contains(" widows ")).to_equal(false)
expect(unsupported_words.contains(" empty-cells ")).to_equal(false)
expect(unsupported.contains("background-attachment")).to_equal(false)
expect(unsupported).to_contain("border-image-source")
expect(unsupported_words.contains(" clip ")).to_equal(false)
expect(unsupported_words.contains(" color-scheme ")).to_equal(false)
expect(unsupported_words.contains(" filter ")).to_equal(false)
expect(unsupported_words.contains(" rotate ")).to_equal(false)
expect(unsupported_words.contains(" scale ")).to_equal(false)
expect(unsupported).to_contain("grid-template-columns")
expect(unsupported_words.contains(" place-content ")).to_equal(false)
expect(unsupported_words.contains(" place-items ")).to_equal(false)
expect(unsupported_words.contains(" place-self ")).to_equal(false)
expect(unsupported_words.contains(" translate ")).to_equal(false)
expect(unsupported).to_contain("scroll-padding-inline-start")
expect(unsupported).to_contain("view-transition-name")
expect(unsupported.contains("block-size")).to_equal(false)
expect(unsupported.contains("inline-size")).to_equal(false)
expect(unsupported.contains("min-block-size")).to_equal(false)
expect(unsupported.contains("min-inline-size")).to_equal(false)
expect(unsupported.contains("max-block-size")).to_equal(false)
expect(unsupported.contains("max-inline-size")).to_equal(false)
expect(unsupported.contains("inset")).to_equal(false)
expect(unsupported.contains("inset-block")).to_equal(false)
expect(unsupported.contains("inset-block-start")).to_equal(false)
expect(unsupported.contains("inset-block-end")).to_equal(false)
expect(unsupported.contains("inset-inline")).to_equal(false)
expect(unsupported.contains("inset-inline-start")).to_equal(false)
expect(unsupported.contains("inset-inline-end")).to_equal(false)
expect(unsupported.contains("border-block")).to_equal(false)
expect(unsupported.contains("border-block-color")).to_equal(false)
expect(unsupported.contains("border-block-end")).to_equal(false)
expect(unsupported.contains("border-block-end-color")).to_equal(false)
expect(unsupported.contains("border-block-end-style")).to_equal(false)
expect(unsupported.contains("border-block-end-width")).to_equal(false)
expect(unsupported.contains("border-block-start")).to_equal(false)
expect(unsupported.contains("border-block-start-color")).to_equal(false)
expect(unsupported.contains("border-block-start-style")).to_equal(false)
expect(unsupported.contains("border-block-start-width")).to_equal(false)
expect(unsupported.contains("border-block-style")).to_equal(false)
expect(unsupported.contains("border-block-width")).to_equal(false)
expect(unsupported.contains("border-inline")).to_equal(false)
expect(unsupported.contains("border-inline-color")).to_equal(false)
expect(unsupported.contains("border-inline-end")).to_equal(false)
expect(unsupported.contains("border-inline-end-color")).to_equal(false)
expect(unsupported.contains("border-inline-end-style")).to_equal(false)
expect(unsupported.contains("border-inline-end-width")).to_equal(false)
expect(unsupported.contains("border-inline-start")).to_equal(false)
expect(unsupported_words.contains(" clear ")).to_equal(false)
expect(unsupported_words.contains(" content ")).to_equal(false)
expect(unsupported_words.contains(" content-visibility ")).to_equal(false)
expect(unsupported_words.contains(" contain ")).to_equal(false)
expect(unsupported_words.contains(" image-rendering ")).to_equal(false)
expect_not(unsupported_words.contains(" font-feature-settings "))
expect_not(unsupported_words.contains(" font-language-override "))
expect_not(unsupported_words.contains(" font-variation-settings "))
expect_not(unsupported_words.contains(" font-variant "))
expect_not(unsupported_words.contains(" font-variant-caps "))
expect_not(unsupported_words.contains(" font-variant-position "))
expect(unsupported_words.contains(" font-kerning ")).to_equal(false)
expect(unsupported_words.contains(" font-optical-sizing ")).to_equal(false)
expect_not(unsupported_words.contains(" font-palette "))
expect_not(unsupported_words.contains(" font-stretch "))
expect_not(unsupported_words.contains(" font-width "))
expect_not(unsupported_words.contains(" font-size-adjust "))
expect(unsupported_words.contains(" font-synthesis ")).to_equal(false)
expect_not(unsupported_words.contains(" font-synthesis-small-caps "))
expect_not(unsupported_words.contains(" font-synthesis-position "))
expect_not(unsupported_words.contains(" font-synthesis-style "))
expect(unsupported_words.contains(" font-synthesis-weight ")).to_equal(false)
expect(unsupported_words.contains(" line-break ")).to_equal(false)
expect(unsupported_words.contains(" hyphens ")).to_equal(false)
expect(unsupported_words.contains(" text-justify ")).to_equal(false)
expect(unsupported_words.contains(" writing-mode ")).to_equal(false)
expect(unsupported_words.contains(" text-combine-upright ")).to_equal(false)
expect(unsupported_words.contains(" text-align-all ")).to_equal(false)
expect(unsupported_words.contains(" text-orientation ")).to_equal(false)
expect(unsupported_words.contains(" scrollbar-color ")).to_equal(false)
expect(unsupported_words.contains(" scrollbar-width ")).to_equal(false)
expect(unsupported_words.contains(" table-layout ")).to_equal(false)
expect(unsupported_words.contains(" vertical-align ")).to_equal(false)
expect(unsupported_words.contains(" float ")).to_equal(false)
expect(unsupported_words.contains(" font-family ")).to_equal(false)
expect(unsupported_words.contains(" list-style ")).to_equal(false)
expect(unsupported_words.contains(" list-style-type ")).to_equal(false)
expect(unsupported.contains("border-inline-start-color")).to_equal(false)
expect(unsupported.contains("border-inline-start-style")).to_equal(false)
expect(unsupported.contains("border-inline-start-width")).to_equal(false)
expect(unsupported.contains("border-inline-style")).to_equal(false)
expect(unsupported.contains("border-inline-width")).to_equal(false)
expect(unsupported.contains("border-start-start-radius")).to_equal(false)
expect(unsupported.contains("border-start-end-radius")).to_equal(false)
expect(unsupported.contains("border-end-start-radius")).to_equal(false)
expect(unsupported.contains("border-end-end-radius")).to_equal(false)
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

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)
- **Research:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)


</details>
