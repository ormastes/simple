# Index Bracket Validation Specification

> <details>

<!-- sdn-diagram:id=index_bracket_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_bracket_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_bracket_validation_spec -> core
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_bracket_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Index Bracket Validation Specification

## Scenarios

### core bracket expression validation

#### rejects comparison in index position

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return s[1 == 0]")).to_equal(true)
```

</details>

#### rejects logical and in index position

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[true and false]")).to_equal(true)
```

</details>

#### rejects logical not in index position

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[not false]")).to_equal(true)
```

</details>

#### rejects comparison slice start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return len(s[1 < 2:2])")).to_equal(true)
```

</details>

#### rejects comparison slice end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_fails("fn main() -> i64:\n    val s = \"abc\"\n    return len(s[0:1 == 1])")).to_equal(true)
```

</details>

#### still allows arithmetic indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_fails("fn main() -> i64:\n    val arr = [1, 2, 3]\n    return arr[1 + 1]")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/core/index_bracket_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- core bracket expression validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
