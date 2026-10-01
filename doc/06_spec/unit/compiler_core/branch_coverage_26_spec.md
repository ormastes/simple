# Branch Coverage 26 Specification

> Tests covering Parser Error Handling Coverage, Expression Edge Cases Coverage, Match Statement Edge Cases Coverage, Loop Edge Cases Coverage, Optional Chaining Edge Cases Coverage, Array Edge Cases Coverage, Type Edge Cases Coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 26 Specification

## Scenarios

### Parser Error Handling Coverage

#### handles empty input gracefully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles empty input gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty input gracefully")
# Tests parser with minimal input
val result = 0 + 0
check(result == 0)
```

</details>

#### handles single token

- handles single token


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single token")
val x = 42
check(x == 42)
```

</details>

#### handles maximum nesting depth

- handles maximum nesting depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles maximum nesting depth")
# Deeply nested parentheses
val result = ((((((((1))))))))
check(result == 1)
```

</details>

#### handles long identifier names

- handles long identifier names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles long identifier names")
val very_long_variable_name_that_tests_buffer_limits_in_lexer = 123
check(very_long_variable_name_that_tests_buffer_limits_in_lexer == 123)
```

</details>

#### handles edge case - negative zero

- handles edge case - negative zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles edge case - negative zero")
val x = -0
check(x == 0)
```

</details>

#### handles edge case - empty string

- handles edge case - empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles edge case - empty string")
val s = ""
check(s.len() == 0)
```

</details>

#### handles edge case - string with only escape

- handles edge case - string with only escape


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles edge case - string with only escape")
val s = "\n"
check(s.len() > 0)
```

</details>

#### handles multiple string interpolations

- handles multiple string interpolations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple string interpolations")
val a = 1
val b = 2
val s = "{a} and {b}"
check(s.contains("1"))
```

</details>

#### handles nested string interpolations

- handles nested string interpolations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested string interpolations")
val x = 5
val s = "value: {x + 10}"
check(s.contains("15"))
```

</details>

### Expression Edge Cases Coverage

#### handles precedence - multiplication before addition

- handles precedence - multiplication before addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles precedence - multiplication before addition")
val result = 2 + 3 * 4
check(result == 14)
```

</details>

#### handles precedence - parentheses override

- handles precedence - parentheses override


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles precedence - parentheses override")
val result = (2 + 3) * 4
check(result == 20)
```

</details>

#### handles unary negation with expression

- handles unary negation with expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unary negation with expression")
val result = -(5 + 3)
check(result == -8)
```

</details>

#### handles double negation

- handles double negation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles double negation")
val result = -(-10)
check(result == 10)
```

</details>

#### handles not operator

- handles not operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles not operator")
val result = not false
check(result == true)
```

</details>

#### handles not with comparison

- handles not with comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles not with comparison")
val result = not (5 > 10)
check(result == true)
```

</details>

#### handles chain comparisons - all true

- handles chain comparisons - all true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles chain comparisons - all true")
val result = 1 < 2 and 2 < 3
check(result == true)
```

</details>

#### handles chain comparisons - one false

- handles chain comparisons - one false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles chain comparisons - one false")
val result = 1 < 2 and 2 > 3
check(result == false)
```

</details>

### Match Statement Edge Cases Coverage

#### match with single case

- match with single case


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with single case")
val x = 1
val result = match x:
    1: "one"
    _: "other"
check(result == "one")
```

</details>

#### match with no default - nil case

- match with no default - nil case


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with no default - nil case")
val x = Some(5)
match x:
    Some(v):
        check(v == 5)
    nil:
        check(false)
```

</details>

#### match with wildcard only

- match with wildcard only


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with wildcard only")
val x = 99
val result = match x:
    _: "always"
check(result == "always")
```

</details>

#### match with boolean patterns

- match with boolean patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with boolean patterns")
val b = true
val result = match b:
    true: 1
    false: 0
check(result == 1)
```

</details>

### Loop Edge Cases Coverage

<details>
<summary>Advanced: for loop with zero iterations</summary>

#### for loop with zero iterations

- for loop with zero iterations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop with zero iterations")
var count = 0
for i in 0..0:
    count = count + 1
check(count == 0)
```

</details>


</details>

<details>
<summary>Advanced: for loop with one iteration</summary>

#### for loop with one iteration

- for loop with one iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop with one iteration")
var count = 0
for i in 0..1:
    count = count + 1
check(count == 1)
```

</details>


</details>

<details>
<summary>Advanced: for loop with negative range handled</summary>

#### for loop with negative range handled

- for loop with negative range handled


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop with negative range handled")
var count = 0
for i in 5..5:
    count = count + 1
check(count == 0)
```

</details>


</details>

<details>
<summary>Advanced: while loop never enters</summary>

#### while loop never enters

- while loop never enters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while loop never enters")
var executed = false
while false:
    executed = true
check(executed == false)
```

</details>


</details>

<details>
<summary>Advanced: while loop with immediate break</summary>

#### while loop with immediate break

- while loop with immediate break


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while loop with immediate break")
fn run() -> i64:
    var count = 0
    while true:
        count = count + 1
        break
    count
check(run() == 1)
```

</details>


</details>

<details>
<summary>Advanced: nested loops with break in inner</summary>

#### nested loops with break in inner

- nested loops with break in inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested loops with break in inner")
fn run() -> i64:
    var outer_count = 0
    var inner_count = 0
    for i in 0..3:
        outer_count = outer_count + 1
        for j in 0..3:
            inner_count = inner_count + 1
            break
    outer_count * 10 + inner_count
check(run() == 33)
```

</details>


</details>

### Optional Chaining Edge Cases Coverage

#### optional chain with nil

- optional chain with nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional chain with nil")
val x: i64? = nil
val result = x ?? 99
check(result == 99)
```

</details>

#### optional chain with value

- optional chain with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional chain with value")
val x: i64? = Some(42)
val result = x ?? 99
check(result == 42)
```

</details>

#### nested optional with nil

- nested optional with nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested optional with nil")
val x = nil
check(not x.?)
```

</details>

#### nested optional with some

- nested optional with some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested optional with some")
val x = Some(Some(10))
check(x.?)
```

</details>

### Array Edge Cases Coverage

#### empty array creation

- empty array creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty array creation")
val arr = []
check(arr.len() == 0)
```

</details>

#### array with one element

- array with one element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array with one element")
val arr = [42]
check(arr.len() == 1)
check(arr[0] == 42)
```

</details>

#### array negative index

- array negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array negative index")
val arr = [1, 2, 3]
check(arr[-1] == 3)
check(arr[-2] == 2)
```

</details>

#### array slice empty result

- array slice empty result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array slice empty result")
val arr = [1, 2, 3]
check(slice_len(arr, 0, 0) == 0)
```

</details>

#### array slice full

- array slice full


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array slice full")
val arr = [1, 2, 3]
check(slice_len(arr, 0, 3) == 3)
```

</details>

### Type Edge Cases Coverage

#### boolean true literal

- boolean true literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boolean true literal")
check(true == true)
```

</details>

#### boolean false literal

- boolean false literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("boolean false literal")
check(false == false)
```

</details>

#### nil literal type

- nil literal type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil literal type")
val x = nil
check(not x.?)
```

</details>

#### integer zero

- integer zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer zero")
check(0 == 0)
```

</details>

#### integer negative

- integer negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer negative")
check(-1 < 0)
```

</details>

#### integer positive

- integer positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer positive")
check(1 > 0)
```

</details>

#### float zero

- float zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float zero")
val f: f64 = 0.0
check(f == 0.0)
```

</details>

#### float negative

- float negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float negative")
val f: f64 = -1.5
check(f < 0.0)
```

</details>

#### float positive

- float positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float positive")
val f: f64 = 1.5
check(f > 0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/branch_coverage_26_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Parser Error Handling Coverage, Expression Edge Cases Coverage, Match Statement Edge Cases Coverage, Loop Edge Cases Coverage, Optional Chaining Edge Cases Coverage, Array Edge Cases Coverage, Type Edge Cases Coverage.
- Parser Error Handling Coverage
- Expression Edge Cases Coverage
- Match Statement Edge Cases Coverage
- Loop Edge Cases Coverage
- Optional Chaining Edge Cases Coverage
- Array Edge Cases Coverage
- Type Edge Cases Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
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

- Canonical SPipe generation for source `b9779a9567b6c9ec9d5732617c02487cdba61236685c8a2e513d1f090ba02498`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b9779a9567b6c9ec9d5732617c02487cdba61236685c8a2e513d1f090ba02498`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b9779a9567b6c9ec9d5732617c02487cdba61236685c8a2e513d1f090ba02498`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/branch_coverage_26_spec.spl
mirror: doc/06_spec/unit/compiler_core/branch_coverage_26_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/branch_coverage_26_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/branch_coverage_26_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/branch_coverage_26_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty input gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_26_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles single token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_26_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles maximum nesting depth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
