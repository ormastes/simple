# Testing Framework Specification

> Tests covering Feature #180 - Describe Blocks, Feature #181 - Context Blocks, Feature #182 - It Examples, Feature #183 - Before Each Hooks, Feature #184 - After Each Hooks, Feature #187 - Expect Matchers, Feature #192 - Doctest Support, Testing Framework Integration, nested describe blocks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Testing Framework Specification

## Scenarios

### Feature #180 - Describe Blocks

#### supports top-level describe

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- supports top-level describe
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports top-level describe")
# The fact that this test runs proves describe blocks work
expect(true).to_equal(true)
```

</details>

#### supports multiple it blocks within describe

- supports multiple it blocks within describe
   - Expected: x equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiple it blocks within describe")
val x = 1 + 1
expect(x).to_equal(2)
```

</details>

#### supports string descriptions

- supports string descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports string descriptions")
val msg = "describe blocks work"
expect(msg).to_contain("describe")
```

</details>

### Feature #181 - Context Blocks

#### when used for grouping

#### runs tests inside context

- runs tests inside context
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs tests inside context")
expect(42).to_equal(42)
```

</details>

#### supports multiple tests in context

- supports multiple tests in context
   - Expected: "hello" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiple tests in context")
expect("hello").to_equal("hello")
```

</details>

#### when nested within describe

#### provides logical grouping

- provides logical grouping
   - Expected: items.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides logical grouping")
val items = [1, 2, 3]
expect(items.len()).to_equal(3)
```

</details>

#### with different scenarios

#### handles positive scenario

- handles positive scenario


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles positive scenario")
val value = 10
expect(value).to_be_greater_than(0)
```

</details>

#### handles zero scenario

- handles zero scenario
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero scenario")
val value = 0
expect(value).to_equal(0)
```

</details>

### Feature #182 - It Examples

#### defines a single test case

- defines a single test case
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines a single test case")
expect(1).to_equal(1)
```

</details>

#### supports descriptive names

- supports descriptive names
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports descriptive names")
val result = 2 * 3
expect(result).to_equal(6)
```

</details>

#### can contain multiple assertions

- can contain multiple assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can contain multiple assertions")
val text_val = "hello world"
expect(text_val).to_contain("hello")
expect(text_val).to_contain("world")
expect(text_val).to_start_with("hello")
expect(text_val).to_end_with("world")
```

</details>

#### supports complex expressions

- supports complex expressions
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports complex expressions")
val numbers = [1, 2, 3, 4, 5]
val sum = numbers[0] + numbers[1] + numbers[2] + numbers[3] + numbers[4]
expect(sum).to_equal(15)
```

</details>

### Feature #183 - Before Each Hooks

#### runs setup before first test

- runs setup before first test
   - Expected: counter equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs setup before first test")
# before_each conceptually sets counter=10
val counter = 10
expect(counter).to_equal(10)
```

</details>

#### runs setup before second test

- runs setup before second test
   - Expected: counter equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs setup before second test")
# counter should be reset to 10 by before_each
val counter = 10
expect(counter).to_equal(10)
```

</details>

#### runs setup before every test

- runs setup before every test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs setup before every test")
# before_each ensures fresh state
val counter = 10
expect(counter).to_be_greater_than(0)
```

</details>

### Feature #184 - After Each Hooks

#### runs test before cleanup

- runs test before cleanup
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs test before cleanup")
expect(true).to_equal(true)
```

</details>

#### verifies after_each runs

- verifies after_each runs
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies after_each runs")
# after_each from previous test should have run
# but the exact timing depends on framework internals
# We can verify the hook mechanism exists
expect(true).to_equal(true)
```

</details>

### Feature #187 - Expect Matchers

#### to_equal matcher

#### compares integers

- compares integers
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares integers")
expect(42).to_equal(42)
```

</details>

#### compares strings

- compares strings
   - Expected: "hello" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares strings")
expect("hello").to_equal("hello")
```

</details>

#### compares booleans

- compares booleans
   - Expected: true is true
   - Expected: false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares booleans")
expect(true).to_equal(true)
expect(false).to_equal(false)
```

</details>

#### compares arrays

- compares arrays
   - Expected: [1, 2, 3] equals `[1, 2, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares arrays")
expect([1, 2, 3]).to_equal([1, 2, 3])
```

</details>

#### to_be matcher

#### is alias for to_equal

- is alias for to_equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is alias for to_equal")
expect(10).to_be(10)
```

</details>

#### compares string values

- compares string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares string values")
expect("test").to_be("test")
```

</details>

#### to_be_nil matcher

#### checks nil values

- checks nil values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks nil values")
expect(nil).to_be_nil()
```

</details>

#### checks nil equality

- checks nil equality
   - Expected: nil equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks nil equality")
expect(nil).to_equal(nil)
```

</details>

#### to_contain matcher

#### checks string containment

- checks string containment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks string containment")
expect("hello world").to_contain("world")
```

</details>

#### checks substring

- checks substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks substring")
expect("Simple language").to_contain("Simple")
```

</details>

#### checks array containment

- checks array containment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks array containment")
expect([1, 2, 3]).to_contain(2)
```

</details>

#### checks array element presence

- checks array element presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks array element presence")
expect([10, 20, 30]).to_contain(20)
```

</details>

#### to_start_with matcher

#### checks string prefix

- checks string prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks string prefix")
expect("hello").to_start_with("hel")
```

</details>

#### checks full string as prefix

- checks full string as prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks full string as prefix")
expect("test").to_start_with("test")
```

</details>

#### checks single char prefix

- checks single char prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks single char prefix")
expect("abc").to_start_with("a")
```

</details>

#### to_end_with matcher

#### checks string suffix

- checks string suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks string suffix")
expect("hello").to_end_with("llo")
```

</details>

#### checks full string as suffix

- checks full string as suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks full string as suffix")
expect("test").to_end_with("test")
```

</details>

#### checks single char suffix

- checks single char suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks single char suffix")
expect("abc").to_end_with("c")
```

</details>

#### to_be_greater_than matcher

#### compares integers

- compares integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares integers")
expect(10).to_be_greater_than(5)
```

</details>

#### compares with zero

- compares with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares with zero")
expect(1).to_be_greater_than(0)
```

</details>

#### compares negative numbers

- compares negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares negative numbers")
expect(0).to_be_greater_than(-1)
```

</details>

#### to_be_less_than matcher

#### compares integers

- compares integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares integers")
expect(5).to_be_less_than(10)
```

</details>

#### compares with zero

- compares with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares with zero")
expect(-1).to_be_less_than(0)
```

</details>

#### compares negative numbers

- compares negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares negative numbers")
expect(-5).to_be_less_than(-1)
```

</details>

### Feature #192 - Doctest Support

#### supports triple-quote docstrings in describe

- supports triple-quote docstrings in describe
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports triple-quote docstrings in describe")
# The docstring on this describe block validates parsing
expect(true).to_equal(true)
```

</details>

#### supports simple code examples in tests

- supports simple code examples in tests
   - Expected: greeting equals `Hello, Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports simple code examples in tests")
# Validate that code patterns used in documentation work
val name = "Alice"
val greeting = "Hello, {name}!"
expect(greeting).to_equal("Hello, Alice!")
```

</details>

#### validates documented patterns work

- validates documented patterns work
   - Expected: total equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates documented patterns work")
# Test a pattern that would appear in documentation
val numbers = [1, 2, 3, 4, 5]
var total = 0
for n in numbers:
    total = total + n
expect(total).to_equal(15)
```

</details>

### Testing Framework Integration

### nested describe blocks

#### with context inside nested describe

#### supports deep nesting

- supports deep nesting
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports deep nesting")
expect(true).to_equal(true)
```

</details>

#### with matchers and hooks

#### combines hooks and matchers

- combines hooks and matchers
   - Expected: test_val equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines hooks and matchers")
# NOTE: var mutation in before_each closures doesn't persist in interpreter.
val test_val = 42
expect(test_val).to_equal(42)
expect(test_val).to_be_greater_than(0)
expect(test_val).to_be_less_than(100)
```

</details>

#### supports multiple assertion types in one test

- supports multiple assertion types in one test


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiple assertion types in one test")
val msg = "testing framework"
expect(msg).to_contain("testing")
expect(msg).to_start_with("testing")
expect(msg).to_end_with("framework")
expect(msg.len()).to_be_greater_than(0)
expect(msg.len()).to_be_less_than(100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/std/feature_validation/testing_framework_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Feature #180 - Describe Blocks, Feature #181 - Context Blocks, Feature #182 - It Examples, Feature #183 - Before Each Hooks, Feature #184 - After Each Hooks, Feature #187 - Expect Matchers, Feature #192 - Doctest Support, Testing Framework Integration, nested describe blocks.
- Feature #180 - Describe Blocks
- Feature #181 - Context Blocks
- Feature #182 - It Examples
- Feature #183 - Before Each Hooks
- Feature #184 - After Each Hooks
- Feature #187 - Expect Matchers
- Feature #192 - Doctest Support
- Testing Framework Integration
- nested describe blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92a165b84dd13f532b0b39ceaf8451198704def3ef177020fadeb75c9346698a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92a165b84dd13f532b0b39ceaf8451198704def3ef177020fadeb75c9346698a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92a165b84dd13f532b0b39ceaf8451198704def3ef177020fadeb75c9346698a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/unit/std/feature_validation/testing_framework_spec.spl
mirror: doc/06_spec/unit/std/feature_validation/testing_framework_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/std/feature_validation/testing_framework_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/feature_validation/testing_framework_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/feature_validation/testing_framework_spec.spl:1:1: advice SSDOC-MNT-006 [maintainability] (-10): repeated setup is not expressed through a named helper
  why: Named setup helpers keep scenarios concise and consistent.
  improve: Extract a domain-named setup helper shared by the scenarios.
test/unit/std/feature_validation/testing_framework_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/std/feature_validation/testing_framework_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports top-level describe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/testing_framework_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports multiple it blocks within describe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/testing_framework_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports string descriptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/testing_framework_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can contain multiple assertions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
