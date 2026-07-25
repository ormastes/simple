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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cut Specification

## Scenarios

### cut tool

#### range parsing

#### parses single field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ranges = parse_ranges("2")
expect(ranges.len()).to_equal(1)
expect(ranges[0].0).to_equal(2)
expect(ranges[0].1).to_equal(2)
```

</details>

#### parses field range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ranges = parse_ranges("1-3")
expect(ranges.len()).to_equal(1)
expect(ranges[0].0).to_equal(1)
expect(ranges[0].1).to_equal(3)
```

</details>

#### parses multiple fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ranges = parse_ranges("1,3,5")
expect(ranges.len()).to_equal(3)
```

</details>

#### range checking

#### detects position in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ranges = [(1, 3)]
expect(is_in_ranges(2, ranges)).to_equal(true)
```

</details>

#### rejects position outside range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ranges = [(1, 3)]
expect(is_in_ranges(5, ranges)).to_equal(false)
```

</details>

#### field cutting

#### extracts single field with tab delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cut_fields("a\tb\tc", [(2, 2)], "\t", false)
expect(result).to_equal("b")
```

</details>

#### extracts field range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cut_fields("a\tb\tc\td", [(2, 3)], "\t", false)
expect(result).to_equal("b\tc")
```

</details>

#### character cutting

#### extracts characters by position

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cut_chars("hello", [(1, 3)])
expect(result).to_equal("hel")
```

</details>

#### extracts single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cut_chars("hello", [(2, 2)])
expect(result).to_equal("e")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/cut_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cut tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
