# Animations Wpt Specification

> <details>

<!-- sdn-diagram:id=animations_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=animations_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

animations_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=animations_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Animations Wpt Specification

## Scenarios

### WPT-derived CSS animations subset

#### CSS animation pure function coverage

#### interpolate_length at t=0.5 returns midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = interpolate_length(0.0, 100.0, 0.5)
expect(approx(result, 50.0)).to_equal(true)
```

</details>

#### ease_value linear returns identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ease_value(0.5, TimingFunction.Linear)
expect(approx(result, 0.5)).to_equal(true)
```

</details>

#### ease_value ease-in starts slow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ease_value(0.5, TimingFunction.EaseIn)
expect(result < 0.5).to_equal(true)
```

</details>

#### interpolate Number values at midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_interp_number_half()).to_equal(true)
```

</details>

#### extract_keyframes parses @keyframes block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = "@keyframes fade { from { opacity: 0; } to { opacity: 1; } }"
val registry = extract_keyframes(css)
expect(registry.entries.len() >= 1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/animations_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived CSS animations subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
