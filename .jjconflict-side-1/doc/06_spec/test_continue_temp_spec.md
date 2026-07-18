# Test Continue Temp Specification

> <details>

<!-- sdn-diagram:id=test_continue_temp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_continue_temp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_continue_temp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_continue_temp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Continue Temp Specification

## Scenarios

### continue in for

#### continue works

- results push
   - Expected: results.len() equals `2`
   - Expected: results[0] equals `a`
   - Expected: results[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results: [text] = []
val items = ["a", "b", "c"]
for item in items:
    if item == "b":
        continue
    results.push(item)
expect(results.len()).to_equal(2)
expect(results[0]).to_equal("a")
expect(results[1]).to_equal("c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_continue_temp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- continue in for

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
