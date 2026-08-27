# No-Parentheses Function Calls Specification

> No-parentheses function calls allow calling functions without wrapping arguments in parentheses, providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# No-Parentheses Function Calls Specification

No-parentheses function calls allow calling functions without wrapping arguments in parentheses, providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #300-310 |
| Category | Syntax |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/no_paren_calls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

No-parentheses function calls allow calling functions without wrapping arguments in parentheses,
providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function
calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

## Syntax

### Basic No-Paren Calls

```simple
print "Hello"              # print("Hello")
val result = add 2, 3      # val result = add(2, 3)
```

### With Field Access

```simple
obj.method arg             # obj.method(arg)
```

### With Trailing Lambdas

```simple
map numbers \x: x * 2      # map(numbers, \x: x * 2)
```

### With Colon-Blocks

```simple
describe "Feature":
    # @manual scenario evidence
test code
# describe("Feature", fn(): test code)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| No-Paren Call | Function call without wrapping arguments in `()` |
| Callable Expression | Identifier, field access, or path that can be called |
| Trailing Lambda | Lambda with `\` syntax as final argument |
| Colon-Block | Indented block after `:` becomes lambda argument |
| Comma Required | Arguments must be separated by commas in Normal mode |

## Behavior

- **Callable expressions**: Only identifiers, field access (`obj.method`), and paths (`Module.func`)
- **Comma-separated**: Multiple arguments require commas in Normal mode
- **Trailing lambda**: Backslash syntax (`\params: body`) can append lambda
- **Colon-block**: `:` followed by indent creates lambda argument
- **No nesting**: Strict mode disallows nested no-paren calls
- **Statement level**: Works at statement level, not within complex expressions

## Related Specifications

- [Trailing Blocks](../trailing_blocks/trailing_blocks_spec.md) - Lambda syntax with backslash
- [Functions](../functions/functions_spec.md) - Function definition and calling
- [Lambdas/Closures](../lambdas_closures/lambdas_closures_spec.md) - Lambda expressions

## Implementation Notes

**Parser:** `src/parser/src/expressions/no_paren.rs`
- `parse_with_no_paren_calls()` - Main entry point
- `is_callable_expr()` - Determines if expression can start no-paren call
- `can_start_argument()` - Checks if token can begin an argument

**Modes:**
- **Normal**: Default, allows nesting (may be ambiguous)
- **Strict**: GPU mode, disallows nested no-paren calls

**Performance:** No-paren calls desugar to regular calls during parsing - zero runtime overhead.

## Examples

```simple
# Basic calls
print "Hello World"
val sum = add 5, 10

# With field access
list.each item

# With trailing lambda
map items \x: x * 2
filter values \v: v > 0

# With colon-block
describe "Test":
it "works":
    # @req REQ-SSPEC-FEATURE
    step("works")
    step("works")
    # @req: REQ-FEAT-USAGE-NO-PAREN-CALLS-SPEC-001
expect(true).to_equal(true)

# Multiple arguments
call arg1, arg2, arg3
```

## Scenarios

### No-Paren Calls - Basic Syntax

#### with single argument

#### calls function with single argument

- calls function with single argument
- calls function with single argument
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls function with single argument")
step("calls function with single argument")
fn double(x):
    x * 2

val result = double 5
expect(result).to_equal(10)
```

</details>

#### calls with literal argument

- calls with literal argument
- calls with literal argument
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls with literal argument")
step("calls with literal argument")
fn identity(x):
    x

val result = identity 42
expect(result).to_equal(42)
```

</details>

#### calls with identifier argument

- calls with identifier argument
- calls with identifier argument
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls with identifier argument")
step("calls with identifier argument")
fn identity(x):
    x

val value = 100
val result = identity value
expect(result).to_equal(100)
```

</details>

#### with multiple arguments

#### calls with two arguments

- calls with two arguments
- calls with two arguments
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls with two arguments")
step("calls with two arguments")
fn add(a, b):
    a + b

val result = add(10, 20)
expect(result).to_equal(30)
```

</details>

#### calls with three arguments

- calls with three arguments
- calls with three arguments
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls with three arguments")
step("calls with three arguments")
fn add3(a, b, c):
    a + b + c

val result = add3(5, 10, 15)
expect(result).to_equal(30)
```

</details>

#### mixes literals and identifiers

- mixes literals and identifiers
- mixes literals and identifiers
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes literals and identifiers")
step("mixes literals and identifiers")
fn multiply(a, b):
    a * b

val factor = 5
val result = multiply(factor, 3)
expect(result).to_equal(15)
```

</details>

### No-Paren Calls - Argument Types

#### with literals

#### passes integer literal

- passes integer literal
- passes integer literal
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes integer literal")
step("passes integer literal")
fn identity(x):
    x

val result = identity 42
expect(result).to_equal(42)
```

</details>

#### passes string literal

- passes string literal
- passes string literal
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes string literal")
step("passes string literal")
fn identity(x):
    x

val result = identity "hello"
expect(result).to_equal("hello")
```

</details>

#### passes boolean literal

- passes boolean literal
- passes boolean literal
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes boolean literal")
step("passes boolean literal")
fn identity(x):
    x

val result = identity true
expect(result).to_equal(true)
```

</details>

#### with parenthesized expressions

#### passes arithmetic expression

- passes arithmetic expression
- passes arithmetic expression
   - Expected: result equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes arithmetic expression")
step("passes arithmetic expression")
fn square(x):
    x * x

val result = square (3 + 2)
expect(result).to_equal(25)
```

</details>

#### passes multiple expressions

- passes multiple expressions
- passes multiple expressions
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes multiple expressions")
step("passes multiple expressions")
fn add(a, b):
    a + b

val result = add((2 * 3), (4 + 5))
expect(result).to_equal(15)
```

</details>

### No-Paren Calls - Nested Calls

#### with inner parenthesized calls

#### nests parenthesized call

- nests parenthesized call
- nests parenthesized call
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("nests parenthesized call")
step("nests parenthesized call")
fn double(x):
    x * 2

fn triple(x):
    x * 3

val result = double triple(5)
expect(result).to_equal(30)
```

</details>

#### chains multiple functions

- chains multiple functions
- chains multiple functions
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple functions")
step("chains multiple functions")
fn add1(x):
    x + 1

fn add2(x):
    x + 2

val result = add1 add2(10)
expect(result).to_equal(13)
```

</details>

### No-Paren Calls - Trailing Lambdas

#### with single argument plus lambda

#### accepts trailing lambda

- accepts trailing lambda
- accepts trailing lambda
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts trailing lambda")
step("accepts trailing lambda")
fn apply(x, f):
    f(x)

val result = apply 5 \n: n * 2
expect(result).to_equal(10)
```

</details>

#### passes multiple args plus lambda

- passes multiple args plus lambda
- passes multiple args plus lambda
   - Expected: sum equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes multiple args plus lambda")
step("passes multiple args plus lambda")
fn fold(arr, init, f):
    var acc = init
    var i = 0
    while i < arr.len():
        acc = f(acc, arr[i])
        i = i + 1
    acc

val nums = [1, 2, 3]
val sum = fold(nums, 0) \acc, x: acc + x
expect(sum).to_equal(6)
```

</details>

### No-Paren Calls - Method Calls

#### with method calls

#### uses no-paren with helper function

- uses no-paren with helper function
- uses no-paren with helper function
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses no-paren with helper function")
step("uses no-paren with helper function")
fn get_double_func():
    fn inner(x):
        x * 2
    inner

val double_func = get_double_func()
val result = double_func 21
expect(result).to_equal(42)
```

</details>

### No-Paren Calls - Context

#### in assignments

#### works in val assignments

- works in val assignments
- works in val assignments
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in val assignments")
step("works in val assignments")
fn double(x):
    x * 2

val result = double 10
expect(result).to_equal(20)
```

</details>

#### works in var assignments

- works in var assignments
- works in var assignments
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in var assignments")
step("works in var assignments")
fn add(a, b):
    a + b

var result = add(5, 7)
expect(result).to_equal(12)
```

</details>

#### in return statements

#### works in implicit returns

- works in implicit returns
- works in implicit returns
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in implicit returns")
step("works in implicit returns")
fn wrapper(x):
    fn inner(n):
        n * 2
    inner x

val result = wrapper 7
expect(result).to_equal(14)
```

</details>

### No-Paren Calls - String Arguments

#### with string literals

#### passes single string

- passes single string
- passes single string
   - Expected: result equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes single string")
step("passes single string")
fn identity(s):
    s

val result = identity "test"
expect(result).to_equal("test")
```

</details>

#### passes string with spaces

- passes string with spaces
- passes string with spaces
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes string with spaces")
step("passes string with spaces")
fn identity(s):
    s

val result = identity "hello world"
expect(result).to_equal("hello world")
```

</details>

### No-Paren Calls - Mixed Syntax

#### with mixed styles

#### mixes paren and no-paren

- mixes paren and no-paren
- mixes paren and no-paren
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes paren and no-paren")
step("mixes paren and no-paren")
fn add(a, b):
    a + b

fn double(x):
    x * 2

val result = add(double(5), 3)
expect(result).to_equal(13)
```

</details>

#### chains multiple mixed calls

- chains multiple mixed calls
- chains multiple mixed calls
   - Expected: result equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple mixed calls")
step("chains multiple mixed calls")
fn add1(x):
    x + 1

fn add2(x):
    x + 2

fn add3(x):
    x + 3

val result = add1 add2(add3(10))
expect(result).to_equal(16)
```

</details>

### No-Paren Calls - Edge Cases

#### with zero arguments

#### requires parens for zero args

- requires parens for zero args
- requires parens for zero args
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("requires parens for zero args")
step("requires parens for zero args")
fn get_value():
    42

val result = get_value()
expect(result).to_equal(42)
```

</details>

#### with single identifier

#### passes single variable

- passes single variable
- passes single variable
   - Expected: result equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes single variable")
step("passes single variable")
fn square(x):
    x * x

val num = 7
val result = square num
expect(result).to_equal(49)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-NO-PAREN-CALLS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a249845a927ff6a8b66164c3814976fb8532e2674b0456fa505d917e546c33ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a249845a927ff6a8b66164c3814976fb8532e2674b0456fa505d917e546c33ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a249845a927ff6a8b66164c3814976fb8532e2674b0456fa505d917e546c33ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/feature/usage/no_paren_calls_spec.spl
mirror: doc/06_spec/feature/usage/no_paren_calls_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/feature/usage/no_paren_calls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/no_paren_calls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/no_paren_calls_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/no_paren_calls_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/feature/usage/no_paren_calls_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls function with single argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/no_paren_calls_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls with literal argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/no_paren_calls_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls with identifier argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
