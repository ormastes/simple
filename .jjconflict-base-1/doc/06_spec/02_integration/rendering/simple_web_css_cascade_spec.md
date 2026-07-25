# Simple Web Css Cascade Specification

> <details>

<!-- sdn-diagram:id=simple_web_css_cascade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_css_cascade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_css_cascade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_css_cascade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Css Cascade Specification

## Scenarios

### simple web css cascade

#### keeps higher specificity after candidate merge sorting

- Build rules where a lower-specificity class rule appears after a higher-specificity compound rule
- Resolve the target height through computed style
- Assert the higher-specificity selector still wins
   - Expected: height equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build rules where a lower-specificity class rule appears after a higher-specificity compound rule")
val html = _cascade_fixture("div.target{height:33px}.target{height:21px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the higher-specificity selector still wins")
expect(height).to_equal("33")
```

</details>

#### keeps source order for equal specificity candidates

- Build two equal-specificity class rules that both match the target
- Resolve the target height through computed style
- Assert the later equal-specificity rule wins
   - Expected: height equals `29`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build two equal-specificity class rules that both match the target")
val html = _cascade_fixture(".target{height:17px}.hot{height:29px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the later equal-specificity rule wins")
expect(height).to_equal("29")
```

</details>

#### deduplicates a selector-list rule reached through tag and class buckets

- Build a selector-list rule that can enter through both tag and class buckets
- Resolve the target height through computed style
- Assert the later class rule still wins after the selector-list rule is merged once
   - Expected: height equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a selector-list rule that can enter through both tag and class buckets")
val html = _cascade_fixture("div,.target{height:41px}.hot{height:23px}")
step("Resolve the target height through computed style")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the later class rule still wins after the selector-list rule is merged once")
expect(height).to_equal("23")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_css_cascade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple web css cascade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
