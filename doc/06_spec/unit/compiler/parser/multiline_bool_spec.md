# Multiline Bool Specification

> Tests covering Multiline Boolean Expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multiline Bool Specification

## Scenarios

### Multiline Boolean Expressions

#### allows simple multiline and in parentheses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows simple multiline and in parentheses
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows simple multiline and in parentheses")
val result = (true and
    true)
expect(result).to_equal(true)
```

</details>

#### allows multiline and with false

- allows multiline and with false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows multiline and with false")
val result = (true and
    false)
expect(result).to_equal(false)
```

</details>

#### allows multiline or in parentheses

- allows multiline or in parentheses
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows multiline or in parentheses")
val result = (false or
    true)
expect(result).to_equal(true)
```

</details>

#### allows three-way and expression

- allows three-way and expression
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows three-way and expression")
val result = (true and
    true and
    true)
expect(result).to_equal(true)
```

</details>

#### allows three-way mixed expression

- allows three-way mixed expression
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows three-way mixed expression")
val a = true
val b = false
val c = true
val ab = (a and b)
val result = (ab or c)
expect(result).to_equal(true)
```

</details>

#### allows nested parentheses with multiline

- allows nested parentheses with multiline
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows nested parentheses with multiline")
val result = (true and (false or
    true))
expect(result).to_equal(true)
```

</details>

#### allows complex nested expression

- allows complex nested expression
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows complex nested expression")
val inner = (false or true)
val middle = (true and inner)
val result = (true and middle)
expect(result).to_equal(true)
```

</details>

#### works in if statement condition

- works in if statement condition
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works in if statement condition")
val a = true
val b = true
val c = true
var result = false
if (a and
    b and
    c):
    result = true
expect(result).to_equal(true)
```

</details>

#### works with comparison operators

- works with comparison operators
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with comparison operators")
val x = 5
val result = (x > 3 and
    x < 10)
expect(result).to_equal(true)
```

</details>

#### works with function calls

- works with function calls
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with function calls")
fn is_positive(n: i64) -> bool:
    n > 0
fn is_even(n: i64) -> bool:
    n % 2 == 0
val n = 4
val result = (is_positive(n) and
    is_even(n))
expect(result).to_equal(true)
```

</details>

#### allows multiline with not operator

- allows multiline with not operator
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows multiline with not operator")
val result = (not false and
    true)
expect(result).to_equal(true)
```

</details>

#### allows four-level deep nesting

- allows four-level deep nesting
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows four-level deep nesting")
val d = (true or false)
val c = (false and d)
val b = (true or c)
val result = (true and b)
expect(result).to_equal(true)
```

</details>

#### works with multiple conditions in while

- works with multiple conditions in while
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with multiple conditions in while")
fn run_while() -> i64:
    var count = 0
    var i = 0
    while (i < 5 and
        count < 10):
        count = count + 1
        i = i + 1
    count
val count = run_while()
expect(count).to_equal(5)
```

</details>

#### works in if with multiline condition in match case

- works in if with multiline condition in match case
   - Expected: result equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works in if with multiline condition in match case")
val x = 10
val in_range = (x > 5 and x < 15)
var result = "other"
if x == 10:
    if in_range:
        result = "yes"
    else:
        result = "no"
expect(result).to_equal("yes")
```

</details>

#### works with string comparisons

- works with string comparisons
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with string comparisons")
val name = "Alice"
val result = (name == "Alice" and
    name.len() > 3)
expect(result).to_equal(true)
```

</details>

#### allows very long multiline expression

- allows very long multiline expression
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows very long multiline expression")
val a = true
val b = (a and a and a and a)
val result = (b and a and a and a)
expect(result).to_equal(true)
```

</details>

#### works with array membership

- works with array membership
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with array membership")
val items = [1, 2, 3, 4, 5]
val x = 3
val result = (x in items and
    x > 0)
expect(result).to_equal(true)
```

</details>

#### works with null coalescing

- works with null coalescing
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with null coalescing")
val x = 5
val maybe = x
val lo = (maybe ?? 0 > 0)
val hi = (maybe ?? 0 < 10)
val result = (lo and hi)
expect(result).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/multiline_bool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Multiline Boolean Expressions.
- Multiline Boolean Expressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `978d0e8e0b59afbb69ddc44eeb8031e3d2b47027a691b9a9829ab6bfc06e4bbd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `978d0e8e0b59afbb69ddc44eeb8031e3d2b47027a691b9a9829ab6bfc06e4bbd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `978d0e8e0b59afbb69ddc44eeb8031e3d2b47027a691b9a9829ab6bfc06e4bbd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/parser/multiline_bool_spec.spl
mirror: doc/06_spec/unit/compiler/parser/multiline_bool_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/multiline_bool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/multiline_bool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/multiline_bool_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/multiline_bool_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows simple multiline and in parentheses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/multiline_bool_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows multiline and with false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/multiline_bool_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows multiline or in parentheses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
