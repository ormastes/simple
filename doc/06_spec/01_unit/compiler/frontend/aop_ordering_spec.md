# Aop Ordering Specification

> Tests covering AOP Advice Ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Ordering Specification

## Scenarios

### AOP Advice Ordering

#### sorts by priority descending

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sorts by priority descending
   - Expected: sorted[0].advice_function equals `high_pri`
   - Expected: sorted[1].advice_function equals `low_pri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sorts by priority descending")
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

- breaks priority tie with specificity
   - Expected: sorted[0].advice_function equals `high_spec`
   - Expected: sorted[1].advice_function equals `low_spec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("breaks priority tie with specificity")
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

- breaks specificity tie with lexicographic name
   - Expected: sorted[0].advice_function equals `aaa_fn`
   - Expected: sorted[1].advice_function equals `zzz_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("breaks specificity tie with lexicographic name")
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

- sorts three items correctly
   - Expected: sorted[0].advice_function equals `high`
   - Expected: sorted[1].advice_function equals `mid`
   - Expected: sorted[2].advice_function equals `low`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sorts three items correctly")
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

- handles empty list
   - Expected: sorted.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles empty list")
val items: [MatchedAdvice] = []
val sorted = sort_matched_by_priority(items)
expect(sorted.len()).to_equal(0)
```

</details>

#### handles single item

- handles single item
   - Expected: sorted.len() equals `1`
   - Expected: sorted[0].advice_function equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles single item")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AOP Advice Ordering.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e52d54584465f5882fb103efe3c565370895715ca07d23ac60f84be4b25b787e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e52d54584465f5882fb103efe3c565370895715ca07d23ac60f84be4b25b787e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e52d54584465f5882fb103efe3c565370895715ca07d23ac60f84be4b25b787e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/frontend/aop_ordering_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/aop_ordering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/aop_ordering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/aop_ordering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/aop_ordering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/aop_ordering_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts by priority descending' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/aop_ordering_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'breaks priority tie with specificity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/aop_ordering_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'breaks specificity tie with lexicographic name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
