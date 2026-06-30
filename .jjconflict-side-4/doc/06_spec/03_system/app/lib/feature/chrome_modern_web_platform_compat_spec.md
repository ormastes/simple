# Chrome Modern Web Platform Compat Specification

> <details>

<!-- sdn-diagram:id=chrome_modern_web_platform_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_modern_web_platform_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_modern_web_platform_compat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_modern_web_platform_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome Modern Web Platform Compat Specification

## Scenarios

### Chrome modern web platform compatibility plan

#### REQ-001 compatibility matrix

<details>
<summary>Advanced: should require HTML CSS DOM rendering and JavaScript matrix coverage</summary>

#### should require HTML CSS DOM rendering and JavaScript matrix coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("HTML, CSS, DOM/rendering, and JavaScript")
expect(plan).to_contain("web_platform_feature_matrix.md")
```

</details>


</details>

#### should require explicit compatibility statuses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("`supported`, `partial`, `missing`, or `not-applicable`")
```

</details>

#### should gate migration on first WPT and Test262 subset selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("identify the first WPT/Test262 subset to migrate")
```

</details>

#### REQ-002 WPT subset migration

#### should define a repeatable WPT subset import surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("tools/wpt_to_spipe/")
expect(plan).to_contain("test/feature/web_platform/")
```

</details>

#### should provide the first executable WPT selector color subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset_plan = _read(WPT_SUBSET_PLAN_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(subset_plan).to_contain("selector_color_subset_spec.spl")
expect(subset_plan).to_contain("At least 25 selected WPT-shaped cases")
expect(subset_spec).to_contain("WPT-derived CSS selector and color subset")
expect(subset_spec).to_contain("covers partial :has descendant matching")
```

</details>

#### should cover selector color parser and rendering basics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("CSS selectors")
expect(plan).to_contain("CSS colors")
expect(plan).to_contain("HTML parser basics")
expect(plan).to_contain("Rendering basics")
```

</details>

#### should cover CSS custom property fallback colors in the WPT selector subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers CSS custom property fallback colors")
expect(spec).to_contain("covers CSS custom property fallback colors in background shorthand")
```

</details>

#### should require at least twenty five WPT derived cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("At least 25 selected WPT-derived cases")
```

</details>

#### REQ-003 Test262 subset migration

#### should define a repeatable Test262 subset import surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("tools/test262_to_spipe/")
expect(plan).to_contain("test/js/test262_subset/")
```

</details>

#### should classify JavaScript conformance outcomes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("expected-pass, expected-fail, and unsupported-host")
```

</details>

#### should require at least fifty stable Test262 derived cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("At least 50 selected Test262-derived cases")
```

</details>

#### REQ-004 supported feature evidence

#### should require SPipe or external suite mapping for supported features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("Every supported feature has SPipe coverage or an explicit external-suite mapping")
```

</details>

#### should cover universal selectors in the WPT selector subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(WPT_SELECTOR_COLOR_SPEC_PATH)).to_contain("covers universal selector matching")
```

</details>

#### should cover modern is selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(RENDERER_SPEC_PATH)).to_contain("applies :is selector lists in fallback pixels")
```

</details>

#### should cover modern where selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(RENDERER_SPEC_PATH)).to_contain("applies :where selector lists in fallback pixels")
```

</details>

#### should cover modern not selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :not selector lists in fallback pixels")
expect(spec).to_contain("rejects :not selectors when an option matches")
```

</details>

#### should cover partial has selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :has descendant selectors in fallback pixels")
expect(spec).to_contain("applies :has direct child selectors in fallback pixels")
expect(spec).to_contain("rejects :has direct child selectors for nested descendants")
expect(spec).to_contain("rejects :has selectors when no descendant option matches")
```

</details>

#### should cover bounded descendant combinators in the WPT selector subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers descendant combinator matching")
expect(spec).to_contain("covers descendant combinator sibling rejection")
```

</details>

#### should cover bounded direct child combinators in the WPT selector subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers direct child combinator matching")
expect(spec).to_contain("covers ancestor child combinator matching")
expect(spec).to_contain("covers ancestor child combinator nested descendant rejection")
expect(spec).to_contain("covers direct child combinator nested descendant rejection")
```

</details>

#### should cover bounded adjacent sibling combinators in the WPT selector subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers adjacent sibling combinator matching")
expect(spec).to_contain("covers adjacent sibling combinator non-adjacent rejection")
```

</details>

#### should cover bounded general sibling combinators in the WPT selector subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(spec).to_contain("covers general sibling combinator matching")
expect(spec).to_contain("covers general sibling combinator preceding-source rejection")
```

</details>

#### should cover partial empty selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :empty selectors in fallback pixels")
expect(spec).to_contain("rejects :empty selectors when the fallback div has content")
```

</details>

#### should cover partial first child selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :first-child selectors in fallback pixels")
expect(spec).to_contain("rejects :first-child selectors for later fallback divs")
```

</details>

#### should cover partial last child selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :last-child selectors in fallback pixels")
expect(spec).to_contain("rejects :last-child selectors for earlier fallback divs")
```

</details>

#### should cover partial only child selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :only-child selectors in fallback pixels")
expect(spec).to_contain("rejects :only-child selectors when a sibling exists")
```

</details>

#### should cover partial nth child selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies :nth-child odd and even selectors in fallback pixels")
expect(spec).to_contain("rejects :nth-child odd selectors for even fallback nodes")
expect(spec).to_contain("applies :nth-child an plus b selectors in fallback pixels")
expect(spec).to_contain("rejects :nth-child an plus b selectors for non matching fallback nodes")
```

</details>

#### should cover simple CSS layer block behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies simple rules nested inside CSS layer blocks")
expect(spec).to_contain("applies functional selectors nested inside CSS layer blocks")
```

</details>

#### should cover simple CSS nesting behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("normalizes simple CSS nesting before fallback selector scans")
expect(spec).to_contain("applies simple CSS nesting with parent selector references")
expect(spec).to_contain("applies simple descendant rules from CSS nesting")
```

</details>

#### should cover basic attribute selector behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies attribute presence selectors in fallback pixels")
expect(spec).to_contain("applies exact attribute value selectors in fallback pixels")
expect(spec).to_contain("applies exact quoted attribute value selectors containing spaces")
expect(spec).to_contain("rejects exact attribute value selectors with different values")
```

</details>

#### should cover bounded attribute selector operator behavior in renderer SPipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = _read(RENDERER_SPEC_PATH)
expect(spec).to_contain("applies attribute prefix selectors in fallback pixels")
expect(spec).to_contain("applies attribute suffix selectors in fallback pixels")
expect(spec).to_contain("rejects attribute suffix selectors without a matching suffix")
expect(spec).to_contain("applies attribute substring selectors in fallback pixels")
expect(spec).to_contain("applies attribute whitespace token selectors in fallback pixels")
expect(spec).to_contain("applies attribute dash match selectors in fallback pixels")
expect(spec).to_contain("rejects attribute dash match selectors without a boundary")
expect(spec).to_contain("applies case insensitive attribute selectors in fallback pixels")
expect(spec).to_contain("keeps attribute selectors case sensitive without the i flag")
expect(spec).to_contain("applies explicit case sensitive attribute selectors in fallback pixels")
expect(spec).to_contain("rejects explicit case sensitive attribute selectors with different case")
```

</details>

#### REQ-005 unsupported feature tracking

#### should explicitly reject full Chrome compatibility claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val audit = _read(AUDIT_PATH)
expect(audit).to_contain("Simple is not a full Chrome-compatible browser engine")
```

</details>

#### should require unsupported high value feature tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = _read(FEATURE_REQ_PATH)
expect(req).to_contain("Every unsupported high-value feature shall be recorded")
```

</details>

#### should list broad WPT Test262 HTML and CSS gaps

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val audit = _read(AUDIT_PATH)
expect(audit).to_contain("No complete WPT migration yet")
expect(audit).to_contain("No complete Test262 migration yet")
expect(audit).to_contain("HTML modern element semantics")
expect(audit).to_contain("CSS modern layout systems")
```

</details>

#### REQ-006 verification gate

#### should define PASS WARN and FAIL states

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("STATUS: PASS")
expect(plan).to_contain("STATUS: WARN")
expect(plan).to_contain("STATUS: FAIL")
```

</details>

#### should require the broad library check command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(plan).to_contain("bin/simple check src/lib")
```

</details>

#### should reject manual visual inspection as the only signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = _read(FEATURE_REQ_PATH)
val nfr = _read(NFR_REQ_PATH)
expect(req).to_contain("without relying on manual visual inspection")
expect(nfr).to_contain("shall not depend on manual visual inspection")
```

</details>

#### REQ-007 initial modern CSS BDD slice

#### should implement is and where selector matching in style blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(STYLE_BLOCK_PATH)
expect(source).to_contain(":is() and :where()")
expect(source).to_contain("functional_selector_list_matches")
```

</details>

#### should avoid splitting fallback selector lists inside functional pseudos

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(BROWSER_RENDERER_PATH)
expect(source).to_contain("paren_depth")
expect(source).to_contain("br_functional_selector_contains")
```

</details>

#### should implement partial not and has selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
expect(style_source).to_contain("not_selector_list_matches")
expect(style_source).to_contain("has_descendant_selector_list_match")
expect(style_source).to_contain("node_has_direct_child_matching")
expect(renderer_source).to_contain("br_style_block_rule_for_has_descendant")
expect(renderer_source).to_contain("br_simple_direct_child_option_in_subtree")
expect(renderer_source).to_contain("br_selector_matches_not_self")
expect(style_source).to_contain("node_is_empty")
expect(renderer_source).to_contain("br_style_block_rule_for_empty_self")
expect(style_source).to_contain(":first-child")
expect(renderer_source).to_contain("br_style_block_rule_for_first_child_self")
expect(style_source).to_contain(":last-child")
expect(renderer_source).to_contain("br_style_block_rule_for_last_child_self")
expect(style_source).to_contain(":only-child")
expect(renderer_source).to_contain("br_style_block_rule_for_only_child_self")
expect(style_source).to_contain("nth_child_argument_matches")
expect(style_source).to_contain("nth_child_common_formula_matches")
expect(renderer_source).to_contain("br_style_block_rule_for_nth_child_self")
```

</details>

#### should flatten simple CSS layer blocks before existing rule scans

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("flatten_layer_blocks")
expect(renderer_source).to_contain("br_flatten_layer_blocks")
expect(subset_spec).to_contain("covers simple rules nested inside CSS layer blocks")
```

</details>

#### should flatten simple CSS nesting before existing rule scans

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("flatten_simple_nested_rules")
expect(renderer_source).to_contain("br_flatten_simple_nested_rules")
expect(subset_spec).to_contain("covers simple parent selector CSS nesting")
```

</details>

#### should implement basic attribute selector matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("attribute_selector_matches")
expect(style_source).to_contain("marker == \"$\"")
expect(renderer_source).to_contain("br_style_block_rule_for_attr_self")
expect(subset_spec).to_contain("covers attribute presence selector matching")
expect(subset_spec).to_contain("covers exact attribute value selector matching")
```

</details>

#### should implement bounded attribute selector operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style_source = _read(STYLE_BLOCK_PATH)
val renderer_source = _read(BROWSER_RENDERER_PATH)
val subset_spec = _read(WPT_SELECTOR_COLOR_SPEC_PATH)
expect(style_source).to_contain("sb_attr_value_matches")
expect(renderer_source).to_contain("br_attr_value_matches")
expect(subset_spec).to_contain("covers attribute prefix selector matching")
expect(subset_spec).to_contain("covers attribute substring selector matching")
expect(subset_spec).to_contain("covers attribute whitespace token selector matching")
expect(subset_spec).to_contain("covers attribute dash match selector matching")
expect(style_source).to_contain("sb_attr_has_i_flag")
expect(style_source).to_contain("sb_attr_has_s_flag")
expect(renderer_source).to_contain("br_attr_has_i_flag")
expect(renderer_source).to_contain("br_attr_has_s_flag")
expect(subset_spec).to_contain("covers case insensitive attribute selector matching")
expect(subset_spec).to_contain("covers explicit case sensitive attribute selector matching")
```

</details>

#### should trace the BDD slice through the system test plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_plan = _read(TEST_PLAN_PATH)
expect(test_plan).to_contain("REQ-007: Initial Modern CSS BDD Slice")
expect(test_plan).to_contain("attribute selector/operator, `:empty`, `:first-child`, `:last-child`, and `:only-child` examples should pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/lib/feature/chrome_modern_web_platform_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chrome modern web platform compatibility plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
