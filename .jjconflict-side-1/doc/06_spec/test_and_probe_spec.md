# Test And Probe Specification

> <details>

<!-- sdn-diagram:id=test_and_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_and_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_and_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_and_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test And Probe Specification

## Scenarios

### and probe

#### starts_with and ends_with combined

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "print(\"hello\")"
val sw = s.starts_with("print(")
val ew = s.ends_with(")")
expect(sw).to_equal(true)
expect(ew).to_equal(true)
val both = sw and ew
expect(both).to_equal(true)
```

</details>

#### combined in if

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "print(\"hello\")"
var hit = false
if s.starts_with("print(") and s.ends_with(")"):
    hit = true
expect(hit).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_and_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- and probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
