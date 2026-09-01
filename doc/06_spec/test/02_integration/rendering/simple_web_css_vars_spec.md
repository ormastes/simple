# Simple Web Css Vars Specification

> <details>

<!-- sdn-diagram:id=simple_web_css_vars_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_css_vars_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_css_vars_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_css_vars_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Css Vars Specification

## Scenarios

### simple web css variables

#### resolves used CSS variables while skipping unused root variables

- Build a CSS fixture with several unused root variables and one used height variable
- Resolve the computed target height through the Simple Web style path
- Assert the used variable still resolves after unused variables are skipped
   - Expected: height equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a CSS fixture with several unused root variables and one used height variable")
val html = _css_var_fixture()
step("Resolve the computed target height through the Simple Web style path")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert the used variable still resolves after unused variables are skipped")
expect(height).to_equal("27")
```

</details>

#### resolves CSS variables collected across separate style blocks

- Build a CSS fixture with root variables and use sites split across style tags
- Resolve the computed target height through the joined custom property path
- Assert split style blocks still share collected custom properties
   - Expected: height equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a CSS fixture with root variables and use sites split across style tags")
val html = _multi_style_css_var_fixture()
step("Resolve the computed target height through the joined custom property path")
val height = simple_web_layout_debug_style_by_id(html, "target", "height")
step("Assert split style blocks still share collected custom properties")
expect(height).to_equal("31")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/simple_web_css_vars_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple web css variables

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
