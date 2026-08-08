# Test Currentcolor2 Specification

> <details>

<!-- sdn-diagram:id=test_currentcolor2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_currentcolor2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_currentcolor2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_currentcolor2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Currentcolor2 Specification

## Scenarios

### currentColor

#### color before currentColor bg

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sfcc("<html><body><div style='width: 80px; height: 40px; color: #123456; background-color: currentColor'></div></body></html>", 0xFF123456u32)).to_equal(true)
```

</details>

#### currentColor bg before color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sfcc("<html><body><div style='width: 80px; height: 40px; background-color: currentColor; color: #456789'></div></body></html>", 0xFF456789u32)).to_equal(true)
```

</details>

#### bg shorthand currentColor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sfcc("<html><body><div style='width: 80px; height: 40px; color: #345678; background: currentColor no-repeat'></div></body></html>", 0xFF345678u32)).to_equal(true)
```

</details>

#### existing hardcoded still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sfcc("<html><body style='background-color: currentColor; color: #456789'></body></html>", 0xFF456789u32)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_currentcolor2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- currentColor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
