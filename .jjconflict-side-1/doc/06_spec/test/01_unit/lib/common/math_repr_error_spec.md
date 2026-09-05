# Math Repr Error Specification

> <details>

<!-- sdn-diagram:id=math_repr_error_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_error_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_error_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_error_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Error Specification

## Scenarios

### Math Repr Error Recovery

#### keeps token peeking and numeric fallback helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = math_repr_source()

expect(source).to_contain("fn _peek(tokens: [text], pos: i64) -> text")
expect(source).to_contain("fn _to_int(s: text) -> i64")
expect(source).to_contain("if pos < 0 or pos >= tokens.len():")
expect(source).to_contain("return \"\"")
```

</details>

#### keeps bracket and parenthesis collection helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = math_repr_source()

expect(source).to_contain("fn _collect_bracket(tokens: [text], pos: i64) -> [text]")
expect(source).to_contain("fn _collect_paren(tokens: [text], pos: i64) -> [text]")
expect(source).to_contain("depth = depth + 1")
expect(source).to_contain("depth = depth - 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math_repr_error_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math Repr Error Recovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
