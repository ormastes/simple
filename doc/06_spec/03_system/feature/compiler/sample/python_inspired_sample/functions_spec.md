# Functions (Python-Inspired Sample)

> Tests compilation of function definitions inspired by Python patterns including default parameters, keyword arguments, and closures. Verifies that Python-like function idioms compile and execute correctly via the native backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functions (Python-Inspired Sample)

Tests compilation of function definitions inspired by Python patterns including default parameters, keyword arguments, and closures. Verifies that Python-like function idioms compile and execute correctly via the native backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of function definitions inspired by Python patterns including
default parameters, keyword arguments, and closures. Verifies that Python-like
function idioms compile and execute correctly via the native backend.

## Scenarios

### Functions

#### basic functions

#### defines and calls simple function

- defines and calls simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines and calls simple function")
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(2, 3) == 5
```

</details>

#### uses implicit return

- uses implicit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses implicit return")
fn square(x: i64) -> i64:
    x * x
expect square(4) == 16
```

</details>

#### uses explicit return

- uses explicit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses explicit return")
fn early_return(x: i64) -> i64:
    if x < 0:
        return 0
    x * 2
expect early_return(-5) == 0
expect early_return(5) == 10
```

</details>

#### default parameters

#### uses default when argument omitted

- uses default when argument omitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default when argument omitted")
fn greet(name: text, greeting: text = "Hello") -> text:
    "{greeting}, {name}!"
expect greet("Alice") == "Hello, Alice!"
```

</details>

#### overrides default with explicit value

- overrides default with explicit value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides default with explicit value")
fn greet(name: text, greeting: text = "Hello") -> text:
    "{greeting}, {name}!"
expect greet("Bob", "Hi") == "Hi, Bob!"
```

</details>

#### named arguments

#### passes arguments by name

- passes arguments by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes arguments by name")
fn describe(name: text, age: i64) -> text:
    "{name} is {age} years old"
expect describe(name: "Alice", age: 30) == "Alice is 30 years old"
```

</details>

#### reorders with named arguments

- reorders with named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reorders with named arguments")
fn describe(name: text, age: i64) -> text:
    "{name} is {age} years old"
expect describe(age: 25, name: "Bob") == "Bob is 25 years old"
```

</details>

#### higher-order functions

#### passes function as argument

- passes function as argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes function as argument")
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)
fn double(n: i64) -> i64:
    n * 2
expect apply(double, 5) == 10
```

</details>

#### uses lambda expression

- uses lambda expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lambda expression")
val numbers = [1, 2, 3, 4]
val doubled = numbers.map(_1 * 2)
expect doubled[0] == 2
expect doubled[3] == 8
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `69ceab08024d6fe0d4eab74402bcb69b9ff1ef781be41b9cf022825beb8622a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `69ceab08024d6fe0d4eab74402bcb69b9ff1ef781be41b9cf022825beb8622a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `69ceab08024d6fe0d4eab74402bcb69b9ff1ef781be41b9cf022825beb8622a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines and calls simple function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses implicit return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses explicit return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
