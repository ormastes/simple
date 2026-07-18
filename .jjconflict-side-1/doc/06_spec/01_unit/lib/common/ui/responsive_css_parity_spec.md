# Responsive Css Parity Specification

> <details>

<!-- sdn-diagram:id=responsive_css_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=responsive_css_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

responsive_css_parity_spec -> std
responsive_css_parity_spec -> common
responsive_css_parity_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=responsive_css_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Responsive Css Parity Specification

## Scenarios

### responsive_css — single-source breakpoints, boundary parity with classify()

#### default_breakpoints compact query uses compact_max-1 as max-width

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
val css = responsive_css(bp)
val compact_edge = bp.compact_max - 1
val expected = "@media (max-width: {compact_edge}px)"
expect(css).to_contain(expected)
```

</details>

#### default_breakpoints regular query uses compact_max as min-width and regular_max-1 as max-width

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
val css = responsive_css(bp)
val compact_min = bp.compact_max
val regular_edge = bp.regular_max - 1
val expected = "@media (min-width: {compact_min}px) and (max-width: {regular_edge}px)"
expect(css).to_contain(expected)
```

</details>

#### custom breakpoints (700/1000) produces correct boundary strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = Breakpoints(compact_max: 700, regular_max: 1000)
val css = responsive_css(bp)
expect(css).to_contain("699px")
expect(css).to_contain("700px")
expect(css).to_contain("999px")
```

</details>

#### custom breakpoints (700/1000) does not contain stale default compact boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = Breakpoints(compact_max: 700, regular_max: 1000)
val css = responsive_css(bp)
# 600 should not appear as a max-width media boundary when compact_max is 700
expect(css.contains("(max-width: 600px)")).to_equal(false)
```

</details>

#### stale-literal guard: default breakpoints CSS contains the regular_max-1 boundary, not 1200

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
val css = responsive_css(bp)
val regular_edge = bp.regular_max - 1
# CSS must contain the derived regular boundary
val expected = "{regular_edge}px"
expect(css).to_contain(expected)
# And must not contain stale 1200 unless regular_max IS 1201
# (if regular_max changed from 1200 to 840, then "1200" must not appear as a boundary)
if bp.regular_max != 1201:
    expect(css.contains("(max-width: 1200px)")).to_equal(false)
```

</details>

#### generate_css feeds default_breakpoints into responsive_css (compact query present)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
val compact_edge = bp.compact_max - 1
val expected = "@media (max-width: {compact_edge}px)"
val css = generate_css("modern")
expect(css).to_contain(expected)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/responsive_css_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- responsive_css — single-source breakpoints, boundary parity with classify()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
