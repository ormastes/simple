# Default Parameter Values

> Tests the `default` keyword for function parameter default values using `=` syntax. Covers basic defaults, typed parameters, methods (instance and static), collection defaults, edge cases (booleans, negatives, expressions), and combinations of required and default parameters across functions, classes, and nested scopes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default Parameter Values

Tests the `default` keyword for function parameter default values using `=` syntax. Covers basic defaults, typed parameters, methods (instance and static), collection defaults, edge cases (booleans, negatives, expressions), and combinations of required and default parameters across functions, classes, and nested scopes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-001 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/parser_default_keyword_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `default` keyword for function parameter default values using `=`
syntax. Covers basic defaults, typed parameters, methods (instance and static),
collection defaults, edge cases (booleans, negatives, expressions), and
combinations of required and default parameters across functions, classes,
and nested scopes.

## Syntax

```simple
use std.spec.step

fn greet(name = "World"):
return "Hello, {name}"
fn typed_default(count: i32 = 0):
return count
```

## Scenarios

### Default keyword in function parameters

#### parses default parameter value with = syntax

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses default parameter value with = syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default parameter value with = syntax")
fn greet(name = "World"):
    return "Hello, {name}"
expect greet() == "Hello, World"
expect greet("Alice") == "Hello, Alice"
```

</details>

#### parses multiple default parameters

- parses multiple default parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple default parameters")
fn create_range(min = 0, max = 100):
    return [min, max]
val range = create_range()
expect range[0] == 0
expect range[1] == 100
```

</details>

#### overrides single default parameter

- overrides single default parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides single default parameter")
fn with_defaults(x = 1, y = 2):
    return x + y
expect with_defaults() == 3
expect with_defaults(5) == 7
expect with_defaults(5, 10) == 15
```

</details>

#### parses default with expressions

- parses default with expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default with expressions")
fn with_expr_default(size = 2 ** 10):
    return size
expect with_expr_default() == 1024
```

</details>

#### parses default with arithmetic

- parses default with arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default with arithmetic")
fn compute(base = 100, offset = 10 + 5):
    return base + offset
expect compute() == 115
```

</details>

#### uses default in nested function

- uses default in nested function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default in nested function")
fn outer():
    fn inner(value = 42):
        return value
    return inner()
expect outer() == 42
```

</details>

### Default keyword with types

#### parses default parameter with type annotation

- parses default parameter with type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default parameter with type annotation")
fn typed_default(count: i32 = 0):
    return count
expect typed_default() == 0
expect typed_default(5) == 5
```

</details>

#### parses default text parameter

- parses default text parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default text parameter")
fn with_text(message: text = "default"):
    return message
expect with_text() == "default"
expect with_text("custom") == "custom"
```

</details>

#### parses default float parameter

- parses default float parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default float parameter")
fn with_float(value: f64 = 3.14):
    return value
expect with_float() > 3.0
```

</details>

### Default keyword in methods

#### parses default in class method

- parses default in class method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default in class method")
class Counter:
    value: i32

    me increment(amount = 1):
        self.value = self.value + amount

var c = Counter(value: 10)
c.increment()
expect c.value == 11
```

</details>

#### parses default in static method

- parses default in static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default in static method")
class Factory:
    static fn create(size = 10) -> i32:
        return size

expect Factory.create() == 10
expect Factory.create(20) == 20
```

</details>

### Default keyword with collections

#### parses default empty array

- parses default empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default empty array")
fn with_array(items = []):
    return items.len()
expect with_array() == 0
expect with_array([1, 2, 3]) == 3
```

</details>

#### parses default array literal

- parses default array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default array literal")
fn with_values(data = [1, 2, 3]):
    return data.len()
expect with_values() == 3
```

</details>

### Default keyword edge cases

#### parses default with boolean

- parses default with boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default with boolean")
fn with_flag(enabled = true):
    return enabled
expect with_flag() == true
expect with_flag(false) == false
```

</details>

#### parses default with negative number

- parses default with negative number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default with negative number")
fn with_negative(value = -10):
    return value
expect with_negative() == -10
```

</details>

#### parses default with string interpolation

- parses default with string interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses default with string interpolation")
val default_name = "World"
fn greet_default(name = default_name):
    return "Hello, {name}"
expect greet_default() == "Hello, World"
```

</details>

### Default keyword combinations

#### parses mix of required and default parameters

- parses mix of required and default parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mix of required and default parameters")
fn mixed(required, optional = 5):
    return required + optional
expect mixed(10) == 15
expect mixed(10, 20) == 30
```

</details>

#### parses multiple functions with defaults

- parses multiple functions with defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple functions with defaults")
fn first(x = 1):
    return x
fn second(y = 2):
    return y
expect first() == 1
expect second() == 2
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4edb41b1c4e07968c02c52c43afdd425555ee8aff39b2862eac1e51c21189c4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4edb41b1c4e07968c02c52c43afdd425555ee8aff39b2862eac1e51c21189c4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4edb41b1c4e07968c02c52c43afdd425555ee8aff39b2862eac1e51c21189c4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_default_keyword_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_default_keyword_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_default_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_default_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_default_keyword_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses default parameter value with = syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_default_keyword_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple default parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_default_keyword_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overrides single default parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
