# Sed Specification

> <details>

<!-- sdn-diagram:id=sed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sed_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sed Specification

## Scenarios

### sed tool

#### substitution

#### replaces first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "hello world hello"
val idx = line.find("hello")
val before = line.slice(0, idx)
val after = line.slice(idx + 5, line.len())
val result = "{before}goodbye{after}"
expect(result).to_equal("goodbye world hello")
```

</details>

#### replaces all occurrences with g flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "aaa bbb aaa"
val result = line.replace("aaa", "xxx")
expect(result).to_equal("xxx bbb xxx")
```

</details>

#### deletion

#### deletes lines matching pattern

1. result = result push
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["keep", "remove this", "keep"]
var result: [text] = []
for line in lines:
    if not line.contains("remove"):
        result = result.push(line)
expect(result.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/sed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sed tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
