# Unused Vars Specification

> <details>

<!-- sdn-diagram:id=unused_vars_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unused_vars_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unused_vars_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unused_vars_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unused Vars Specification

## Scenarios

### Unused Variables Lint

#### used variables

#### does not flag variables that are used

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute() -> i64:\n    val x = 10\n    val y = 20\n    x + y\n"
val unused = check_unused_vars_text(code)
val mentions_x = names_contain(unused, "x")
expect(mentions_x).to_equal(false)
```

</details>

#### does not flag variables used in print

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn greet():\n    val greeting = \"Hello\"\n    print greeting\n"
val unused = check_unused_vars_text(code)
val mentions_greeting = names_contain(unused, "greeting")
expect(mentions_greeting).to_equal(false)
```

</details>

#### unused variables

#### flags unused val declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val unused_val = 42\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_unused = names_contain(unused, "unused_val")
expect(mentions_unused).to_equal(true)
```

</details>

#### flags unused var declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    var unused_var = 0\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_unused = names_contain(unused, "unused_var")
expect(mentions_unused).to_equal(true)
```

</details>

#### underscore-prefixed variables

#### does not flag _prefixed variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val _ignored = 42\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_ignored = names_contain(unused, "_ignored")
expect(mentions_ignored).to_equal(false)
```

</details>

#### does not flag single underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    val _ = 42\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_underscore = names_contain(unused, "_")
expect(mentions_underscore).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/unused_vars_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Unused Variables Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
