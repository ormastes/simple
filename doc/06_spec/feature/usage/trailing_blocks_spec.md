# Trailing Blocks Specification

> Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing lambda functions as the last argument to a function or method. They use a backslash (`\`) to introduce parameters, making functional-style code more readable and enabling DSL-like syntax patterns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trailing Blocks Specification

Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing lambda functions as the last argument to a function or method. They use a backslash (`\`) to introduce parameters, making functional-style code more readable and enabling DSL-like syntax patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #450 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/trailing_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing
lambda functions as the last argument to a function or method. They use a backslash (`\`)
to introduce parameters, making functional-style code more readable and enabling DSL-like
syntax patterns.

## Syntax

### Basic Trailing Block

```simple
# Traditional lambda syntax
items.map(_1 * 2)

# Trailing block syntax (cleaner)
items.map \x: x * 2
```

### With Multiple Parameters

```simple
items.reduce(0) \acc, x: acc + x
```

### Block Bodies

```simple
items.each \item:
print(item)
process(item)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Trailing Lambda | Lambda passed as last argument using `\` syntax |
| Backslash Syntax | `\params: body` introduces a trailing block |
| Method Chaining | Trailing blocks work naturally with method chains |
| DSL Support | Enable Ruby-style domain-specific languages |

## Behavior

- **Trailing blocks** are parsed as the last argument to a function/method call
- **Backslash syntax** (`\`) immediately signals a lambda, enabling LL(1) parsing
- **Inline expressions** can be used for simple one-liners: `\x: x * 2`
- **Block bodies** with indentation allow multi-statement blocks
- **Multiple parameters** are comma-separated: `\x, y, z: body`
- **Zero parameters** use empty parameter list: `\: body`
- Works with both **parenthesized** and **no-parentheses** calls

## Related Specifications

- [Lambdas/Closures](../lambdas_closures/lambdas_closures_spec.md) - Lambda syntax and closure semantics
- [No-Parentheses Calls](../no_paren_calls/no_paren_calls_spec.md) - Calling functions without parens
- [Functional Update](../functional_update/functional_update_spec.md) - Functional transformation patterns

## Implementation Notes

**Parser:** `src/parser/src/expressions/postfix.rs`
- `parse_trailing_lambda()` (lines 345-372): Parses trailing block syntax
- `parse_lambda_params()` (lines 377-396): Parses parameter lists

**Integration Points:**
- Function calls with parentheses (line 328-333)
- Method calls with parentheses (line 158-164)
- Method calls without parentheses (line 170-180)
- No-parentheses function calls

**Performance:** Trailing blocks are syntactic sugar - no runtime overhead compared to
traditional lambda syntax. They parse in O(1) time after detecting the backslash token.

## Examples

```simple
# Functional operations
val doubled = [1, 2, 3].map \x: x * 2
val positives = numbers.filter \x: x > 0

# DSL-style router
router.get "/hello" \: "Hello World"
router.post "/user" \request: process(request)

# Method chaining
items.filter \x: x > 0
.map \x: x * 2
.each \x: print(x)
```

## Scenarios

### Trailing Blocks - Basic Syntax

#### with single parameter

#### passes trailing block to function

- passes trailing block to function
- passes trailing block to function
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes trailing block to function")
step("passes trailing block to function")
# @req: REQ-FEAT-USAGE-TRAILING-BLOCKS-SPEC-001
fn apply(x, f):
    f(x)

var result = apply(5) \n: n * 2
expect(result).to_equal(10)
```

</details>

#### works with method-style calls

- works with method-style calls
- works with method-style calls
   - Expected: doubled[0] equals `2`
   - Expected: doubled[1] equals `4`
   - Expected: doubled[2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with method-style calls")
step("works with method-style calls")
fn double_each(arr, f):
    var result = []
    var i = 0
    while i < arr.len():
        result.push(f(arr[i]))
        i = i + 1
    result

val nums = [1, 2, 3]
val doubled = double_each(nums) \x: x * 2
expect(doubled[0]).to_equal(2)
expect(doubled[1]).to_equal(4)
expect(doubled[2]).to_equal(6)
```

</details>

#### with multiple parameters

#### accepts multiple parameters

- accepts multiple parameters
- accepts multiple parameters
   - Expected: sum equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts multiple parameters")
step("accepts multiple parameters")
fn fold(arr, init, f):
    var acc = init
    var i = 0
    while i < arr.len():
        acc = f(acc, arr[i])
        i = i + 1
    acc

val nums = [1, 2, 3, 4]
val sum = fold(nums, 0) \acc, x: acc + x
expect(sum).to_equal(10)
```

</details>

#### works with three parameters

- works with three parameters
- works with three parameters
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with three parameters")
step("works with three parameters")
fn fold3(arr, init, f):
    var acc = init
    var i = 0
    while i < arr.len():
        acc = f(acc, arr[i], i)
        i = i + 1
    acc

val letters = ["a", "b", "c"]
var result = fold3(letters, "") \acc, item, idx: acc + item
expect(result).to_equal("abc")
```

</details>

#### with zero parameters

#### allows zero-parameter blocks

- allows zero-parameter blocks
- allows zero-parameter blocks
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows zero-parameter blocks")
step("allows zero-parameter blocks")
fn call_block(block):
    block()

var result = call_block \: 42
expect(result).to_equal(42)
```

</details>

#### useful for constant responses

- useful for constant responses
- useful for constant responses
   - Expected: response equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("useful for constant responses")
step("useful for constant responses")
fn get_handler(path, handler):
    handler()

val response = get_handler("/health") \: "ok"
expect(response).to_equal("ok")
```

</details>

### Trailing Blocks - Expression Forms

#### with inline expressions

#### evaluates inline expression

- evaluates inline expression
- evaluates inline expression
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates inline expression")
step("evaluates inline expression")
fn transform(x, f):
    f(x)

var result = transform(10) \n: n + 5
expect(result).to_equal(15)
```

</details>

#### supports arithmetic expressions

- supports arithmetic expressions
- supports arithmetic expressions
   - Expected: sum equals `7`
   - Expected: product equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports arithmetic expressions")
step("supports arithmetic expressions")
fn compute(a, b, op):
    op(a, b)

val sum = compute(3, 4) \x, y: x + y
expect(sum).to_equal(7)

val product = compute(3, 4) \x, y: x * y
expect(product).to_equal(12)
```

</details>

#### with block bodies

#### can use traditional lambdas for multi-statement logic

- can use traditional lambdas for multi-statement logic
- can use traditional lambdas for multi-statement logic
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can use traditional lambdas for multi-statement logic")
step("can use traditional lambdas for multi-statement logic")
fn run_block(block):
    block()

var result = run_block(\: 42)

expect(result).to_equal(42)
```

</details>

#### can compute complex expressions inline

- can compute complex expressions inline
- can compute complex expressions inline
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can compute complex expressions inline")
step("can compute complex expressions inline")
fn process(x, handler):
    handler(x)

var result = process(5) \n: (n * 2) + 3

expect(result).to_equal(13)
```

</details>

### Trailing Blocks - Call Contexts

#### with parenthesized calls

#### works with regular function calls

- works with regular function calls
- works with regular function calls
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with regular function calls")
step("works with regular function calls")
fn apply_twice(x, f):
    f(f(x))

var result = apply_twice(3, \n: n + 2)
expect(result).to_equal(7)
```

</details>

#### combines regular args with trailing block

- combines regular args with trailing block
- combines regular args with trailing block
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines regular args with trailing block")
step("combines regular args with trailing block")
fn apply_with_base(base, x, f):
    base + f(x)

var result = apply_with_base(10, 5) \n: n * 2
expect(result).to_equal(20)
```

</details>

#### with no-parentheses calls

#### works without parentheses

- works without parentheses
- works without parentheses
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works without parentheses")
step("works without parentheses")
fn double(x, f):
    f(x)

var result = double 7 \n: n * 2
expect(result).to_equal(14)
```

</details>

### Trailing Blocks - Method Chaining

#### with sequential operations

#### chains filter and map operations

- chains filter and map operations
- chains filter and map operations
   - Expected: doubled[0] equals `2`
   - Expected: doubled[1] equals `6`
   - Expected: doubled[2] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains filter and map operations")
step("chains filter and map operations")
fn filter_list(arr, pred):
    var result = []
    var i = 0
    while i < arr.len():
        if pred(arr[i]):
            result.push(arr[i])
        i = i + 1
    result

fn map_list(arr, f):
    var result = []
    var i = 0
    while i < arr.len():
        result.push(f(arr[i]))
        i = i + 1
    result

val nums = [1, -2, 3, -4, 5]
val filtered = filter_list(nums) \x: x > 0
val doubled = map_list(filtered) \x: x * 2

expect(doubled[0]).to_equal(2)
expect(doubled[1]).to_equal(6)
expect(doubled[2]).to_equal(10)
```

</details>

### Trailing Blocks - DSL Patterns

#### with builder patterns

#### enables DSL-style APIs with trailing blocks

- enables DSL-style APIs with trailing blocks
- enables DSL-style APIs with trailing blocks
   - Expected: result equals `response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("enables DSL-style APIs with trailing blocks")
step("enables DSL-style APIs with trailing blocks")
fn create_handler(response, handler):
    var result = handler()
    expect(result).to_equal(response)

create_handler("ok") \: "ok"
create_handler("hello") \: "hello"
```

</details>

### Trailing Blocks - Edge Cases

#### with nested trailing blocks

#### handles nested trailing blocks

- handles nested trailing blocks
- handles nested trailing blocks
   - Expected: final equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested trailing blocks")
step("handles nested trailing blocks")
fn outer(f):
    fn inner(x):
        f(x)
    inner

var result = outer \x: x * 2
val final = result(5)
expect(final).to_equal(10)
```

</details>

#### with closures

#### captures outer variables

- captures outer variables
- captures outer variables
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures outer variables")
step("captures outer variables")
fn make_adder(base):
    fn add(x, f):
        f(x)
    add

val add10 = make_adder(10)
var captured = 10
var result = add10(5) \x: x + captured
expect(result).to_equal(15)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-TRAILING-BLOCKS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4cae489f58c4ccf48a1133790ce113220cfd4c6cea716e5ec2f8f0202d307ab5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cae489f58c4ccf48a1133790ce113220cfd4c6cea716e5ec2f8f0202d307ab5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cae489f58c4ccf48a1133790ce113220cfd4c6cea716e5ec2f8f0202d307ab5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/feature/usage/trailing_blocks_spec.spl
mirror: doc/06_spec/feature/usage/trailing_blocks_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/trailing_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/trailing_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/trailing_blocks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/trailing_blocks_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes trailing block to function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/trailing_blocks_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with method-style calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/trailing_blocks_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts multiple parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/trailing_blocks_spec.spl:288:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can use traditional lambdas for multi-statement logic' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/trailing_blocks_spec.spl:299:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can compute complex expressions inline' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
