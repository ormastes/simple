# Aop Ordering Specification

> <details>

<!-- sdn-diagram:id=aop_ordering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_ordering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_ordering_spec -> std
aop_ordering_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_ordering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Ordering Specification

## Scenarios

### AOP Advice Ordering

#### sorts by priority descending

- MatchedAdvice
- MatchedAdvice
   - Expected: sorted[0].advice_function equals `high_pri`
   - Expected: sorted[1].advice_function equals `low_pri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    MatchedAdvice(advice_function: "low_pri", form: AdviceForm.Before, priority: 10, specificity: 1),
    MatchedAdvice(advice_function: "high_pri", form: AdviceForm.Before, priority: 50, specificity: 1)
]
val sorted = sort_matched_by_priority(items)
expect(sorted[0].advice_function).to_equal("high_pri")
expect(sorted[1].advice_function).to_equal("low_pri")
```

</details>

#### breaks priority tie with specificity

- MatchedAdvice
- MatchedAdvice
   - Expected: sorted[0].advice_function equals `high_spec`
   - Expected: sorted[1].advice_function equals `low_spec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    MatchedAdvice(advice_function: "low_spec", form: AdviceForm.Before, priority: 10, specificity: 1),
    MatchedAdvice(advice_function: "high_spec", form: AdviceForm.Before, priority: 10, specificity: 4)
]
val sorted = sort_matched_by_priority(items)
expect(sorted[0].advice_function).to_equal("high_spec")
expect(sorted[1].advice_function).to_equal("low_spec")
```

</details>

#### breaks specificity tie with lexicographic name

- MatchedAdvice
- MatchedAdvice
   - Expected: sorted[0].advice_function equals `aaa_fn`
   - Expected: sorted[1].advice_function equals `zzz_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    MatchedAdvice(advice_function: "zzz_fn", form: AdviceForm.Before, priority: 10, specificity: 2),
    MatchedAdvice(advice_function: "aaa_fn", form: AdviceForm.Before, priority: 10, specificity: 2)
]
val sorted = sort_matched_by_priority(items)
expect(sorted[0].advice_function).to_equal("aaa_fn")
expect(sorted[1].advice_function).to_equal("zzz_fn")
```

</details>

#### sorts three items correctly

- MatchedAdvice
- MatchedAdvice
- MatchedAdvice
   - Expected: sorted[0].advice_function equals `high`
   - Expected: sorted[1].advice_function equals `mid`
   - Expected: sorted[2].advice_function equals `low`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    MatchedAdvice(advice_function: "mid", form: AdviceForm.Before, priority: 20, specificity: 2),
    MatchedAdvice(advice_function: "low", form: AdviceForm.Before, priority: 5, specificity: 3),
    MatchedAdvice(advice_function: "high", form: AdviceForm.Before, priority: 100, specificity: 1)
]
val sorted = sort_matched_by_priority(items)
expect(sorted[0].advice_function).to_equal("high")
expect(sorted[1].advice_function).to_equal("mid")
expect(sorted[2].advice_function).to_equal("low")
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [MatchedAdvice] = []
val sorted = sort_matched_by_priority(items)
expect(sorted.len()).to_equal(0)
```

</details>

#### handles single item

- MatchedAdvice
   - Expected: sorted.len() equals `1`
   - Expected: sorted[0].advice_function equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [
    MatchedAdvice(advice_function: "only", form: AdviceForm.Before, priority: 10, specificity: 2)
]
val sorted = sort_matched_by_priority(items)
expect(sorted.len()).to_equal(1)
expect(sorted[0].advice_function).to_equal("only")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_ordering_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP Advice Ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
