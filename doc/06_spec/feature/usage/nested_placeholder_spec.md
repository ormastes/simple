# Nested Placeholder Scoping

> Tests that placeholder lambdas in nested call arguments maintain independent scoping at each nesting level. Verifies that inner and outer placeholders are independent, chained placeholders with nested any/all/filter work correctly, map with nested filter preserves scope, deeply nested chaining, string method placeholders, and edge cases like empty inner lists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nested Placeholder Scoping

Tests that placeholder lambdas in nested call arguments maintain independent scoping at each nesting level. Verifies that inner and outer placeholders are independent, chained placeholders with nested any/all/filter work correctly, map with nested filter preserves scope, deeply nested chaining, string method placeholders, and edge cases like empty inner lists.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/nested_placeholder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that placeholder lambdas in nested call arguments maintain independent scoping at
each nesting level. Verifies that inner and outer placeholders are independent, chained
placeholders with nested any/all/filter work correctly, map with nested filter preserves
scope, deeply nested chaining, string method placeholders, and edge cases like empty
inner lists.

## Scenarios

### Nested Placeholder Scoping

#### method call with nested placeholder

#### scopes inner and outer placeholders independently

- scopes inner and outer placeholders independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scopes inner and outer placeholders independently")
val data = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
val result = data.filter(_.any(_ > 5))
expect result == [[4, 5, 6], [7, 8, 9]]
```

</details>

#### filters arrays that have all elements above threshold

- filters arrays that have all elements above threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filters arrays that have all elements above threshold")
val data = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
val result = data.filter(_.all(_ > 3))
expect result == [[4, 5, 6], [7, 8, 9]]
```

</details>

#### chained placeholders with nested

#### chains outer filter with inner any

- chains outer filter with inner any


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains outer filter with inner any")
val data = [[1, 5], [2, 3], [4, 6]]
val result = data.filter(_.any(_ > 4))
expect result == [[1, 5], [4, 6]]
```

</details>

#### map with nested filter

#### maps then filters within nested context

- maps then filters within nested context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps then filters within nested context")
val data = [[1, 2, 3, 4], [5, 6, 7, 8]]
val result = data.map(_.filter(_ > 2))
expect result == [[3, 4], [5, 6, 7, 8]]
```

</details>

#### simple nested independence

#### outer placeholder is independent of inner

- outer placeholder is independent of inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("outer placeholder is independent of inner")
val nums = [1, 2, 3, 4, 5]
# filter + map as separate operations (each has own _ scope)
val evens = nums.filter(_ % 2 == 0)
val doubled = evens.map(_ * 2)
expect doubled == [4, 8]
```

</details>

#### chained operations maintain separate scopes

- chained operations maintain separate scopes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chained operations maintain separate scopes")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ > 1).map(_ * 3)
expect result == [6, 9, 12, 15]
```

</details>

#### deeply nested

#### handles three levels of nesting via chaining

- handles three levels of nesting via chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles three levels of nesting via chaining")
val data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val result = data.filter(_ > 3).filter(_ < 8).map(_ * 2)
expect result == [8, 10, 12, 14]
```

</details>

#### nested with string methods

#### filters strings containing substrings

- filters strings containing substrings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filters strings containing substrings")
val words = ["hello", "world", "help", "word"]
val result = words.filter(_.len() > 4)
expect result == ["hello", "world"]
```

</details>

#### edge cases

#### nested placeholder on empty inner list

- nested placeholder on empty inner list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("nested placeholder on empty inner list")
val data = [[], [1, 2], []]
val result = data.filter(_.any(_ > 0))
expect result == [[1, 2]]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4cc04180b2637dbe02513e38df2c317ef16085d4910bde74336dc4d01bae5ae2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cc04180b2637dbe02513e38df2c317ef16085d4910bde74336dc4d01bae5ae2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cc04180b2637dbe02513e38df2c317ef16085d4910bde74336dc4d01bae5ae2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/nested_placeholder_spec.spl
mirror: doc/06_spec/feature/usage/nested_placeholder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/nested_placeholder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/nested_placeholder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/nested_placeholder_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scopes inner and outer placeholders independently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/nested_placeholder_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters arrays that have all elements above threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/nested_placeholder_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains outer filter with inner any' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
