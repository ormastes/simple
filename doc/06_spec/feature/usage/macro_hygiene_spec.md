# Macro Hygiene Specification

> Tests for macro hygiene system that prevents variable capture through gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness, and pattern matching with hygiene.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Hygiene Specification

Tests for macro hygiene system that prevents variable capture through gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness, and pattern matching with hygiene.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MACRO-001 |
| Category | Language \| Macros |
| Status | Implemented |
| Source | `test/feature/usage/macro_hygiene_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for macro hygiene system that prevents variable capture through
gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness,
and pattern matching with hygiene.

## Syntax

```simple
macro make_ten() -> (returns result: Int):
emit result:
use std.spec.step

val x = 10
x

val x = 5
val result = make_ten!()
# x is still 5, result is 10
```

## Scenarios

### Basic Macro Hygiene

#### prevents variable capture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prevents variable capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("prevents variable capture")
macro make_ten() -> (returns result: Int):
    emit result:
        val x = 10
        x
val x = 5
val result = make_ten!()
expect x + result == 15
```

</details>

#### isolates macro internal variables

- isolates macro internal variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolates macro internal variables")
macro increment() -> (returns result: Int):
    emit result:
        val temp = 1
        temp
val a = increment!()
val b = increment!()
expect a + b == 2
```

</details>

#### preserves outer variable after macro

- preserves outer variable after macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves outer variable after macro")
macro do_nothing() -> (returns result: Int):
    emit result:
        val value = 100
        value
val value = 42
val _ = do_nothing!()
expect value == 42
```

</details>

### Nested Scope Hygiene

#### handles nested scopes in macro

- handles nested scopes in macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested scopes in macro")
macro nested_scopes() -> (returns result: Int):
    emit result:
        val x = 10
        val inner = if true: 20 else: 0
        x + inner
expect nested_scopes!() == 30
```

</details>

#### handles nested macro calls

- handles nested macro calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested macro calls")
macro inner() -> (returns result: Int):
    emit result:
        val x = 5
        x
macro outer() -> (returns result: Int):
    emit result:
        val x = 10
        x + inner!()
expect outer!() == 15
```

</details>

#### handles nested blocks

- handles nested blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested blocks")
macro nested_blocks() -> (returns result: Int):
    emit result:
        val a = 1
        val b = if true: 2 + 3 else: 0
        a + b
expect nested_blocks!() == 6
```

</details>

### Gensym Uniqueness

#### creates unique names across calls

- creates unique names across calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates unique names across calls")
macro counter() -> (returns result: Int):
    emit result:
        val count = 1
        count
val first = counter!()
val second = counter!()
val third = counter!()
expect first + second + third == 3
```

</details>

#### gensyms multiple variables

- gensyms multiple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gensyms multiple variables")
macro multi_vars() -> (returns result: Int):
    emit result:
        val a = 1
        val b = 2
        val c = 3
        a + b + c
val x = 10
val y = 20
val z = 30
val result = multi_vars!()
expect x + y + z + result == 66
```

</details>

### Pattern Matching Hygiene

#### isolates pattern variables

- isolates pattern variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolates pattern variables")
macro make_pair() -> (returns result: Int):
    emit result:
        val (x, y) = (10, 20)
        x + y
val x = 100
val y = 200
val result = make_pair!()
expect x + y + result == 330
```

</details>

#### isolates tuple destructuring

- isolates tuple destructuring


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolates tuple destructuring")
macro swap_values() -> (returns result: Int):
    emit result:
        val (a, b) = (5, 10)
        b - a
val a = 1
val b = 2
val result = swap_values!()
expect a + b + result == 8
```

</details>

#### isolates array destructuring

- isolates array destructuring


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolates array destructuring")
macro sum_array() -> (returns result: Int):
    emit result:
        val [x, y, z] = [1, 2, 3]
        x + y + z
val x = 10
val y = 20
val z = 30
val result = sum_array!()
expect x + y + z + result == 66
```

</details>

### Function Parameter Hygiene

#### isolates function parameters

- isolates function parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolates function parameters")
macro func_test() -> (returns result: Int):
    emit result:
        fn add(x: Int, y: Int) -> Int:
            return x + y
        add(3, 7)
expect func_test!() == 10
```

</details>

#### isolates function from outer scope

- isolates function from outer scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolates function from outer scope")
macro func_macro() -> (returns result: Int):
    emit result:
        fn multiplier(x: Int) -> Int:
            return x * 2
        multiplier(5)
val x = 100
val result = func_macro!()
expect x + result == 110
```

</details>

#### handles nested functions

- handles nested functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested functions")
macro nested_func() -> (returns result: Int):
    emit result:
        fn outer(x: Int) -> Int:
            fn inner(y: Int) -> Int:
                return x + y
            return inner(5)
        outer(10)
expect nested_func!() == 15
```

</details>

### Complex Macro Hygiene

#### handles complex multi-scope macro

- handles complex multi-scope macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles complex multi-scope macro")
macro complex() -> (returns result: Int):
    emit result:
        val temp = 1
        val sum1 = if true: 2 else: 0
        val sum2 = if true: 3 else: 0
        val sum3 = if true: 4 else: 0
        sum1 + sum2 + sum3 + temp
expect complex!() == 10
```

</details>

#### handles macro parameters

- handles macro parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles macro parameters")
macro use_param(value: Int) -> (returns result: Int):
    emit result:
        val x = value + 10
        x
val x = 5
val result = use_param!(32)
expect x + result == 47
```

</details>

#### handles nested macros with same names

- handles nested macros with same names


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested macros with same names")
macro base(n: Int) -> (returns result: Int):
    emit result:
        val temp = n * 2
        temp
macro wrapper() -> (returns result: Int):
    emit result:
        val temp = 5
        val a = base!(temp)
        val b = base!(10)
        temp + a + b
expect wrapper!() == 35
```

</details>

### Macro Hygiene Edge Cases

#### handles empty macro

- handles empty macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles empty macro")
macro empty() -> (returns result: Int):
    emit result:
        0
expect empty!() == 0
```

</details>

#### handles macro with early return

- handles macro with early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles macro with early return")
macro early_return(cond: Bool) -> (returns result: Int):
    emit result:
        if cond:
            return 100
        val x = 42
        x
expect early_return!(false) == 42
```

</details>

#### handles variable shadowing

- handles variable shadowing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles variable shadowing")
macro shadow_test() -> (returns result: Int):
    emit result:
        val x = 10
        val x = x + 5
        val x = x * 2
        x
expect shadow_test!() == 30
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `ce72d2002f5afd870762e7d37d3909eefde944f1ad181d8526fd1f294cb9ceb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce72d2002f5afd870762e7d37d3909eefde944f1ad181d8526fd1f294cb9ceb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce72d2002f5afd870762e7d37d3909eefde944f1ad181d8526fd1f294cb9ceb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/macro_hygiene_spec.spl
mirror: doc/06_spec/feature/usage/macro_hygiene_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/macro_hygiene_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/macro_hygiene_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/macro_hygiene_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevents variable capture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/macro_hygiene_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'isolates macro internal variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/macro_hygiene_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves outer variable after macro' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
