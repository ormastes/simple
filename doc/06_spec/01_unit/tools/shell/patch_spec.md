# Patch Specification

> 1. result = result push

<!-- sdn-diagram:id=patch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=patch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

patch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=patch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Patch Specification

## Scenarios

### patch tool

#### line operations

#### applies additions

1. result = result push
2. result = result push
3. result = result push
   - Expected: result.len() equals `3`
   - Expected: result[1] equals `new line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = ["line1", "line2"]
var result: [text] = []
result = result.push(original[0])
result = result.push("new line")
result = result.push(original[1])
expect(result.len()).to_equal(3)
expect(result[1]).to_equal("new line")
```

</details>

#### applies deletions

1. result = result push
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = ["line1", "remove", "line3"]
var result: [text] = []
for line in original:
    if line != "remove":
        result = result.push(line)
expect(result.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/patch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- patch tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
