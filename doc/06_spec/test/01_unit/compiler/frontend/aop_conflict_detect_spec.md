# Aop Conflict Detect Specification

> <details>

<!-- sdn-diagram:id=aop_conflict_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_conflict_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_conflict_detect_spec -> std
aop_conflict_detect_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_conflict_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Conflict Detect Specification

## Scenarios

### AOP Conflict Detection

#### returns no conflicts for non-overlapping rules

- WeavingRule
- WeavingRule
   - Expected: conflicts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "log_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "execution(* bar(..))", advice_function: "trace_fn", form: AdviceForm.Before, priority: 20)
]
val conflicts = detect_advice_conflicts(rules)
expect(conflicts.len()).to_equal(0)
```

</details>

#### returns no conflicts for same predicate but different priority

- WeavingRule
- WeavingRule
   - Expected: conflicts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "log_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "trace_fn", form: AdviceForm.Before, priority: 20)
]
val conflicts = detect_advice_conflicts(rules)
expect(conflicts.len()).to_equal(0)
```

</details>

#### returns no conflicts for same predicate and priority but different form

- WeavingRule
- WeavingRule
   - Expected: conflicts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "log_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "trace_fn", form: AdviceForm.AfterSuccess, priority: 10)
]
val conflicts = detect_advice_conflicts(rules)
expect(conflicts.len()).to_equal(0)
```

</details>

#### detects E1504 conflict for same predicate, form, and priority

- WeavingRule
- WeavingRule
   - Expected: conflicts.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "log_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "trace_fn", form: AdviceForm.Before, priority: 10)
]
val conflicts = detect_advice_conflicts(rules)
expect(conflicts.len()).to_equal(1)
expect(conflicts[0].message).to_contain("E1504")
expect(conflicts[0].message).to_contain("log_fn")
expect(conflicts[0].message).to_contain("trace_fn")
```

</details>

#### does not flag same function name as conflict

- WeavingRule
- WeavingRule
   - Expected: conflicts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "log_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "execution(* foo(..))", advice_function: "log_fn", form: AdviceForm.Before, priority: 10)
]
val conflicts = detect_advice_conflicts(rules)
expect(conflicts.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_conflict_detect_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP Conflict Detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
