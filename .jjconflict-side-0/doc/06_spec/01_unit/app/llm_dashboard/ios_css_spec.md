# Ios Css Specification

> <details>

<!-- sdn-diagram:id=ios_css_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ios_css_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ios_css_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ios_css_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ios Css Specification

## Scenarios

### ios_css

### ios_css_overrides

#### AC-5: returns a non-empty CSS string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = ios_css_overrides()
expect(css.len()).to_be_greater_than(0)
```

</details>

#### AC-5: contains -webkit-overflow-scrolling for touch scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = ios_css_overrides()
expect(css).to_contain("-webkit-overflow-scrolling")
```

</details>

#### AC-5: contains iOS accent color #007AFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = ios_css_overrides()
expect(css).to_contain("#007AFF")
```

</details>

#### AC-5: contains 44px touch target min-height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = ios_css_overrides()
expect(css).to_contain("min-height: 44px")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/ios_css_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ios_css
- ios_css_overrides

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
