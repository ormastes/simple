# Method Reference Syntax

> Tests the `&:method` syntax which creates a lambda that calls the given method on its argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map and filter, chaining, storing references as values, usage with various types (strings, arrays), and combining method references with placeholder lambdas.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Reference Syntax

Tests the `&:method` syntax which creates a lambda that calls the given method on its argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map and filter, chaining, storing references as values, usage with various types (strings, arrays), and combining method references with placeholder lambdas.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/method_reference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `&:method` syntax which creates a lambda that calls the given method on its
argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map
and filter, chaining, storing references as values, usage with various types (strings,
arrays), and combining method references with placeholder lambdas.

## Scenarios

### Method Reference

#### basic method reference

#### calls len on strings

- calls len on strings
   - Expected: result equals `[2, 5, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls len on strings")
val words = ["hi", "hello", "hey"]
val result = words.map(&:len)
expect(result).to_equal([2, 5, 3])
```

</details>

#### with filter

#### filters with boolean method

- filters with boolean method
   - Expected: result equals `[[], []]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filters with boolean method")
val data = [[], [1], [], [2, 3]]
val result = data.filter(&:is_empty)
expect(result).to_equal([[], []])
```

</details>

#### chaining method references

#### chains map with method reference

- chains map with method reference
   - Expected: lengths equals `[5, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains map with method reference")
val words = ["hello", "world"]
val lengths = words.map(&:len)
expect(lengths).to_equal([5, 5])
```

</details>

#### method reference as value

#### stores len reference

- stores len reference
   - Expected: get_len("hello") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stores len reference")
val get_len = &:len
expect(get_len("hello")).to_equal(5)
```

</details>

#### method reference with various types

#### calls len on arrays

- calls len on arrays
   - Expected: result equals `[2, 1, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls len on arrays")
val data = [[1, 2], [3], [4, 5, 6]]
val result = data.map(&:len)
expect(result).to_equal([2, 1, 3])
```

</details>

#### edge cases

#### method reference on empty collection

- method reference on empty collection
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("method reference on empty collection")
val data: [text] = []
val result = data.map(&:len)
expect(result).to_equal([])
```

</details>

#### method reference on single element

- method reference on single element
   - Expected: result equals `[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("method reference on single element")
val data = ["hello"]
val result = data.map(&:len)
expect(result).to_equal([5])
```

</details>

#### combines method reference with placeholder

- combines method reference with placeholder
   - Expected: result equals `[5, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines method reference with placeholder")
val words = ["hello", "hi", "hey", "howdy"]
val lengths = words.map(&:len)
val result = lengths.filter(_ > 3)
expect(result).to_equal([5, 5])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `86c4a4adfd4a8fd2406d29316df33a5053c4348bae00d0be243ac76e1cda842c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86c4a4adfd4a8fd2406d29316df33a5053c4348bae00d0be243ac76e1cda842c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86c4a4adfd4a8fd2406d29316df33a5053c4348bae00d0be243ac76e1cda842c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/usage/method_reference_spec.spl
mirror: doc/06_spec/feature/usage/method_reference_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/method_reference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/method_reference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/method_reference_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/method_reference_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls len on strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/method_reference_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters with boolean method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/method_reference_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains map with method reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
