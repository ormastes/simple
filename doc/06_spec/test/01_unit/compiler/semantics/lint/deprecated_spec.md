# Deprecated Specification

> <details>

<!-- sdn-diagram:id=deprecated_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deprecated_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deprecated_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deprecated_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deprecated Specification

## Scenarios

### Deprecated Usage Lint

#### DEPR001 - Type__method() syntax

#### flags Type__method() call pattern as DEPR001

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val result = Vec__new()\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(true)
```

</details>

#### flags String__from() as DEPR001

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val s = String__from(\"hello\")\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(true)
```

</details>

#### does not flag dunder names like __init__

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn __init__():\n    print \"init\"\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(false)
```

</details>

#### does not flag normal function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val x = compute_value()\n"
val codes = check_deprecated_text(code)
val has_depr001 = codes_contain(codes, "DEPR001")
expect(has_depr001).to_equal(false)
```

</details>

#### DEPR002 - .new() constructor

#### flags .new() constructor as DEPR002

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val p = Point.new(1, 2)\n"
val codes = check_deprecated_text(code)
val has_depr002 = codes_contain(codes, "DEPR002")
expect(has_depr002).to_equal(true)
```

</details>

#### does not flag methods named new_item

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val x = create_new_item()\n"
val codes = check_deprecated_text(code)
val has_depr002 = codes_contain(codes, "DEPR002")
expect(has_depr002).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/deprecated_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Deprecated Usage Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
