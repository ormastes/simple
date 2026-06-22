# Sleep Specification

> 1. result = result * 10 +

<!-- sdn-diagram:id=sleep_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sleep_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sleep_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sleep_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sleep Specification

## Scenarios

### sleep tool

#### argument parsing

#### parses integer seconds

1. result = result * 10 +
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "5"
var result: i32 = 0
for ch in s:
    if ch >= "0" and ch <= "9":
        result = result * 10 + (ch.to_i32() - "0".to_i32())
expect(result).to_equal(5)
```

</details>

#### rejects non-numeric input

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
var valid = true
for ch in s:
    if ch < "0" or ch > "9":
        valid = false
expect(valid).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/sleep_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sleep tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
