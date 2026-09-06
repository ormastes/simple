# Unreachable Code Specification

> <details>

<!-- sdn-diagram:id=unreachable_code_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unreachable_code_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unreachable_code_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unreachable_code_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unreachable Code Specification

## Scenarios

### Unreachable Code Lint

#### code after return

#### flags code after return statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test() -> i64:\n    return 42\n    val x = 10\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(true)
```

</details>

#### flags code after return with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute() -> text:\n    return \"done\"\n    print \"never reached\"\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(true)
```

</details>

#### unreachable code has UNREACH001 code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test() -> i64:\n    return 1\n    val dead = 2\n"
val codes = check_unreachable_text(code)
val has_code = codes_contain(codes, "UNREACH001")
expect(has_code).to_equal(true)
```

</details>

#### reachable code

#### does not flag code before return

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test() -> i64:\n    val x = 10\n    return x\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag code in different branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(flag: bool) -> i64:\n    if flag:\n        return 1\n    return 0\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag code after return in nested if

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(x: i64) -> text:\n    if x > 0:\n        return \"positive\"\n    \"non-positive\"\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag empty function body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn noop():\n    pass_do_nothing\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/unreachable_code_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Unreachable Code Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
