# At Supports Wpt Specification

> 1. "@supports

<!-- sdn-diagram:id=at_supports_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=at_supports_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

at_supports_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=at_supports_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# At Supports Wpt Specification

## Scenarios

### WPT CSS @supports

#### @supports conditional rules

#### @supports (display: flex) applies rules

1. "@supports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "@supports (display: flex) { div { width: 12px; height: 8px; background-color: #0891b2; } }",
    "<div></div>",
    0xFF0891B2u32
)).to_equal(true)
```

</details>

#### @supports (display: invalid) rejects known property with invalid value

1. "@supports
   - Expected: not rendered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = _renders_color(
    "@supports (display: definitely-not-css) { div { width: 12px; height: 8px; background-color: #dc2626; } }",
    "<div></div>",
    0xFFDC2626u32
)
expect(not rendered).to_equal(true)
```

</details>

#### @supports (nonexistent: value) does not apply

1. "@supports
   - Expected: not rendered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = _renders_color(
    "@supports (nonexistent: value) { div { width: 12px; height: 8px; background-color: #dc2626; } }",
    "<div></div>",
    0xFFDC2626u32
)
expect(not rendered).to_equal(true)
```

</details>

#### @supports not (nonexistent: value) applies rules

1. "@supports not


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "@supports not (nonexistent: value) { div { width: 12px; height: 8px; background-color: #16a34a; } }",
    "<div></div>",
    0xFF16A34Au32
)).to_equal(true)
```

</details>

#### @supports (text-overflow: ellipsis) applies text rules

1. "@supports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "@supports (text-overflow: ellipsis) { div { width: 12px; height: 8px; background-color: #7c3aed; text-overflow: ellipsis; } }",
    "<div></div>",
    0xFF7C3AEDu32
)).to_equal(true)
```

</details>

#### @supports (text-transform: uppercase) applies text rules

1. "@supports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "@supports (text-transform: uppercase) { div { width: 12px; height: 8px; background-color: #be123c; text-transform: uppercase; } }",
    "<div></div>",
    0xFFBE123Cu32
)).to_equal(true)
```

</details>

#### @supports selector(:has()) applies supported selector rules

1. "@supports selector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_renders_color(
    "@supports selector(div:has(.badge)) { div:has(.badge) { width: 12px; height: 8px; background-color: #0e7490; } }",
    "<div><span class='badge'></span></div>",
    0xFF0E7490u32
)).to_equal(true)
```

</details>

#### @supports selector() rejects unsupported pseudo selectors

1. "@supports selector
   - Expected: not rendered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = _renders_color(
    "@supports selector(div:popover-open) { div { width: 12px; height: 8px; background-color: #dc2626; } }",
    "<div></div>",
    0xFFDC2626u32
)
expect(not rendered).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT CSS @supports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
