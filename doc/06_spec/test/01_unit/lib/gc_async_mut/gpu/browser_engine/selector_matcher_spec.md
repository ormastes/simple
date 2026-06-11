# Selector Matcher Specification

> <details>

<!-- sdn-diagram:id=selector_matcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=selector_matcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

selector_matcher_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=selector_matcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Selector Matcher Specification

## Scenarios

### browser engine selector matcher

#### matches :not when an attribute substring option is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = "a href=\"https://example.test/docs\" class=\"nav\""
expect(br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag)).to_equal(true)
```

</details>

#### rejects :not when an attribute substring option is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = "a href=\"https://example.test/admin\" class=\"nav\""
expect(br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag)).to_equal(false)
```

</details>

#### matches :not with compound class options

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = "button class=\"secondary\""
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(true)
```

</details>

#### rejects :not with compound class options

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = "button class=\"primary\""
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser engine selector matcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
