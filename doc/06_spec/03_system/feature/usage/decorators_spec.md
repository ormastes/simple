# Decorators Specification

> Decorators are functions that transform other functions, enabling aspect-oriented programming patterns like logging, caching, and validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decorators Specification

Decorators are functions that transform other functions, enabling aspect-oriented programming patterns like logging, caching, and validation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DECO-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/03_system/feature/usage/decorators_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Decorators are functions that transform other functions, enabling
aspect-oriented programming patterns like logging, caching, and validation.

## Syntax

```simple
# Basic decorator
@double_result
use std.spec.step

fn add_one(x):
return x + 1

# Decorator with arguments
@multiply_by(3)
fn increment(x):
return x + 1
```

## Scenarios

### Decorators

#### applies basic decorator

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies basic decorator


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies basic decorator")
fn double_result(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@double_result
fn add_one(x):
    return x + 1

expect add_one(5) == 12
```

</details>

#### applies decorator with arguments

- applies decorator with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies decorator with arguments")
fn multiply_by(factor):
    fn decorator(f):
        fn wrapper(x):
            return f(x) * factor
        return wrapper
    return decorator

@multiply_by(3)
fn increment(x):
    return x + 1

expect increment(10) == 33
```

</details>

#### stacks multiple decorators

- stacks multiple decorators


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stacks multiple decorators")
fn add_ten(f):
    fn wrapper(x):
        return f(x) + 10
    return wrapper

fn double(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@add_ten
@double
fn identity(x):
    return x

expect identity(5) == 20  # 5 -> double -> 10 -> add_ten -> 20
```

</details>

#### uses decorator without parentheses

- uses decorator without parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses decorator without parentheses")
fn add_five(f):
    fn wrapper(x):
        return f(x) + 5
    return wrapper

@add_five
fn square(x):
    return x * x

expect square(4) == 21  # 16 + 5
```

</details>

### Attributes

#### uses inline attribute

- uses inline attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses inline attribute")
@inline
fn add(a, b):
    return a + b
expect add(3, 4) == 7
```

</details>

#### uses deprecated attribute

- uses deprecated attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses deprecated attribute")
@deprecated
fn old_api(x):
    return x * 2
expect old_api(10) == 20
```

</details>

#### uses deprecated with message

- uses deprecated with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses deprecated with message")
@deprecated("use new_api instead")
fn legacy(x):
    return x + 1
expect legacy(5) == 6
```

</details>

#### stacks multiple attributes

- stacks multiple attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stacks multiple attributes")
@inline
@deprecated
fn double(x):
    return x * 2
expect double(21) == 42
```

</details>

### Context Managers

#### executes basic with block

- executes basic with block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes basic with block")
var counter = 0
with 42:
    counter = 1
expect counter == 1
```

</details>

#### binds value with as clause

- binds value with as clause


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds value with as clause")
with 42 as x:
    val value = x + 1
expect value == 43
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `b47fb834303cd56b2829347e14249b478e8b975bf9efb6e54c10be08ec14815b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b47fb834303cd56b2829347e14249b478e8b975bf9efb6e54c10be08ec14815b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b47fb834303cd56b2829347e14249b478e8b975bf9efb6e54c10be08ec14815b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/decorators_spec.spl
mirror: doc/06_spec/03_system/feature/usage/decorators_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/decorators_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/decorators_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/decorators_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies basic decorator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/decorators_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies decorator with arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/decorators_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stacks multiple decorators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
