# Find Specification

> <details>

<!-- sdn-diagram:id=find_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=find_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

find_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=find_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Find Specification

## Scenarios

### find tool

#### size filter parsing

#### parses plus prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_size_filter("+100")
expect(result.0).to_equal("+")
expect(result.1).to_equal(100)
```

</details>

#### parses minus prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_size_filter("-50")
expect(result.0).to_equal("-")
expect(result.1).to_equal(50)
```

</details>

#### parses kilobyte suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_size_filter("+1k")
expect(result.0).to_equal("+")
expect(result.1).to_equal(1024)
```

</details>

#### parses megabyte suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_size_filter("+1M")
expect(result.0).to_equal("+")
expect(result.1).to_equal(1048576)
```

</details>

#### size matching

#### matches greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(matches_size(200, "+", 100)).to_equal(true)
```

</details>

#### rejects not greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(matches_size(50, "+", 100)).to_equal(false)
```

</details>

#### matches less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(matches_size(50, "-", 100)).to_equal(true)
```

</details>

#### matches exact size

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(matches_size(100, "", 100)).to_equal(true)
```

</details>

#### depth counting

#### counts zero depth for base path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val depth = count_depth("src", "src")
expect(depth).to_equal(0)
```

</details>

#### counts nested depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val depth = count_depth("src/app/tools", "src")
expect(depth).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/find_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- find tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
