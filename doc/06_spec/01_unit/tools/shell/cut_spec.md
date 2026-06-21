# Cut Specification

> <details>

<!-- sdn-diagram:id=cut_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cut_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cut_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cut_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cut Specification

## Scenarios

### cut tool

#### field extraction

#### extracts fields by delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "one:two:three:four"
val parts = line.split(":")
expect(parts.len()).to_equal(4)
expect(parts[0]).to_equal("one")
expect(parts[2]).to_equal("three")
```

</details>

#### handles tab delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "a\tb\tc"
val parts = line.split("\t")
expect(parts.len()).to_equal(3)
```

</details>

#### character extraction

#### extracts characters by position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "abcdef"
expect(line.char_at(0)).to_equal("a")
expect(line.char_at(2)).to_equal("c")
```

</details>

#### field list parsing

#### parses comma-separated field numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "1,3,5"
val parts = spec.split(",")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/cut_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cut tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
