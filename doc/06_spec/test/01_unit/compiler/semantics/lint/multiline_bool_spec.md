# Multiline Bool Specification

> <details>

<!-- sdn-diagram:id=multiline_bool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multiline_bool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multiline_bool_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multiline_bool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline Bool Specification

## Scenarios

### Multiline Boolean Lint

#### multiline if with trailing boolean operator

#### flags multiline if with trailing and (BOOL001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(a: bool, b: bool):\n    if a and\n       b:\n        print \"both true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(true)
```

</details>

#### flags multiline if with trailing or

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: bool, y: bool):\n    if x or\n       y:\n        print \"either true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(true)
```

</details>

#### single-line boolean

#### does not flag single-line if with and

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(a: bool, b: bool):\n    if a and b:\n        print \"both true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

#### does not flag single-line if with or

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: bool, y: bool):\n    if x or y:\n        print \"either true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

#### parenthesized multiline boolean

#### does not flag parenthesized multiline boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(a: bool, b: bool):\n    if (a and\n        b):\n        print \"both true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

#### does not flag parenthesized multiline or

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: bool, y: bool):\n    if (x or\n        y):\n        print \"either true\"\n"
val warnings = check_multiline_bool(code)
val has_bool001 = warnings_have_code(warnings, "BOOL001")
expect(has_bool001).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/multiline_bool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multiline Boolean Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
