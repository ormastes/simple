# Comprehensive Branch Coverage Test Suite

> Exercises BOTH true AND false branches of every decision type by calling shared functions with different inputs. Same source line must evaluate to both true and false to count as "covered" (deterministic decision IDs).

<!-- sdn-diagram:id=branch_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comprehensive Branch Coverage Test Suite

Exercises BOTH true AND false branches of every decision type by calling shared functions with different inputs. Same source line must evaluate to both true and false to count as "covered" (deterministic decision IDs).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH-COVERAGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler/coverage/branch_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises BOTH true AND false branches of every decision type by calling
shared functions with different inputs. Same source line must evaluate
to both true and false to count as "covered" (deterministic decision IDs).

## Scenarios

### If/Else Decision Coverage

#### covers if-true and if-false via same function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_if_gt(10, 5)).to_equal("above")
expect(branch_if_gt(2, 5)).to_equal("below")
```

</details>

#### covers nested if all paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_nested_if(20)).to_equal("high")
expect(branch_nested_if(12)).to_equal("mid")
expect(branch_nested_if(7)).to_equal("low")
expect(branch_nested_if(2)).to_equal("tiny")
```

</details>

#### covers if without else both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_if_no_else(true)).to_equal("changed")
expect(branch_if_no_else(false)).to_equal("default")
```

</details>

#### covers if expression both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_if_expr(true)).to_equal("yes")
expect(branch_if_expr(false)).to_equal("no")
```

</details>

### While Loop Decision Coverage

#### covers while executed and zero iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_while_loop(5)).to_equal(5)
expect(branch_while_loop(0)).to_equal(0)
```

</details>

#### covers while with break - hit and miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_while_break(3)).to_equal(3)
expect(branch_while_break(200)).to_equal(100)
```

</details>

#### covers while with continue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_while_continue(10)).to_equal(25)
expect(branch_while_continue(0)).to_equal(0)
```

</details>

#### covers while true with break

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_while_true_break(3)).to_equal(3)
expect(branch_while_true_break(1)).to_equal(1)
```

</details>

### For Loop Decision Coverage

#### covers for over non-empty and empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_for_list([1, 2, 3])).to_equal(6)
expect(branch_for_list([])).to_equal(0)
```

</details>

#### covers for range non-empty and empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_for_range(5)).to_equal(5)
expect(branch_for_range(0)).to_equal(0)
```

</details>

#### covers for with break - hit and miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_for_break(4)).to_equal(4)
expect(branch_for_break(200)).to_equal(99)
```

</details>

#### covers for with continue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_for_continue(10)).to_equal(25)
expect(branch_for_continue(0)).to_equal(0)
```

</details>

### Match Decision Coverage

#### covers match all arms

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_match_int(1)).to_equal("one")
expect(branch_match_int(2)).to_equal("two")
expect(branch_match_int(99)).to_equal("other")
```

</details>

#### covers match Some and nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_match_opt(Some(42))).to_equal(42)
expect(branch_match_opt(nil)).to_equal(-1)
```

</details>

#### covers match boolean both

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_match_bool(true)).to_equal("yes")
expect(branch_match_bool(false)).to_equal("no")
```

</details>

### And/Or Short-Circuit Decision Coverage

#### covers and - all combos

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_and(true, true)).to_equal(true)
expect(branch_and(true, false)).to_equal(false)
expect(branch_and(false, true)).to_equal(false)
expect(branch_and(false, false)).to_equal(false)
```

</details>

#### covers or - all combos

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_or(true, true)).to_equal(true)
expect(branch_or(true, false)).to_equal(true)
expect(branch_or(false, true)).to_equal(true)
expect(branch_or(false, false)).to_equal(false)
```

</details>

#### covers and with variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_and_vars(5, 10)).to_equal(true)
expect(branch_and_vars(1, 10)).to_equal(false)
expect(branch_and_vars(5, 3)).to_equal(false)
```

</details>

#### covers or with variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_or_vars(5, 3)).to_equal(true)
expect(branch_or_vars(1, 10)).to_equal(true)
expect(branch_or_vars(1, 3)).to_equal(false)
```

</details>

### Nested Boolean Decision Coverage

#### covers (a and b) or c all combos

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_complex_and_or(true, true, false)).to_equal(true)
expect(branch_complex_and_or(false, true, false)).to_equal(false)
expect(branch_complex_and_or(false, false, true)).to_equal(true)
expect(branch_complex_and_or(false, false, false)).to_equal(false)
```

</details>

#### covers not (a and b) both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_and_or_not(true, true)).to_equal(false)
expect(branch_and_or_not(true, false)).to_equal(true)
```

</details>

#### covers not (a or b) both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_or_not(false, false)).to_equal(true)
expect(branch_or_not(false, true)).to_equal(false)
```

</details>

#### covers nested if with complex boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_nested_if_bool(true, true, false)).to_equal("taken")
expect(branch_nested_if_bool(false, true, false)).to_equal("skipped")
```

</details>

### Option Decision Coverage

#### covers option existence both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_option_check(Some(42))).to_equal(1)
expect(branch_option_check(nil)).to_equal(-1)
```

</details>

#### covers nil coalesce both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_coalesce(Some(10), 0)).to_equal(10)
expect(branch_coalesce(nil, 99)).to_equal(99)
```

</details>

### Comparison Decision Coverage

#### covers equals both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_cmp_eq(5, 5)).to_equal(true)
expect(branch_cmp_eq(5, 3)).to_equal(false)
```

</details>

#### covers not-equals both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_cmp_neq(5, 3)).to_equal(true)
expect(branch_cmp_neq(5, 5)).to_equal(false)
```

</details>

#### covers less-than both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_cmp_lt(3, 5)).to_equal(true)
expect(branch_cmp_lt(5, 3)).to_equal(false)
```

</details>

#### covers greater-than both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_cmp_gt(5, 3)).to_equal(true)
expect(branch_cmp_gt(3, 5)).to_equal(false)
```

</details>

#### covers less-equal both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_cmp_lte(5, 5)).to_equal(true)
expect(branch_cmp_lte(6, 5)).to_equal(false)
```

</details>

#### covers greater-equal both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_cmp_gte(5, 5)).to_equal(true)
expect(branch_cmp_gte(4, 5)).to_equal(false)
```

</details>

### Mixed Control Flow Decision Coverage

#### covers early return both ways

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_early_return(5)).to_equal(true)
expect(branch_early_return(-3)).to_equal(false)
```

</details>

<details>
<summary>Advanced: covers loop with if/else inside</summary>

#### covers loop with if/else inside

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = branch_loop_with_cond(10)
expect(result[0]).to_equal(5)
expect(result[1]).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: covers nested loops with break</summary>

#### covers nested loops with break

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_nested_break(3, 2)).to_equal(6)
expect(branch_nested_break(3, 0)).to_equal(0)
```

</details>


</details>

#### covers while with match inside

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(branch_while_match(4)).to_equal(60)
expect(branch_while_match(0)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
