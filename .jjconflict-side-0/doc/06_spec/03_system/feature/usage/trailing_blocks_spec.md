# Trailing Blocks Specification

> Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing lambda functions as the last argument to a function or method. They use a backslash (`\`) to introduce parameters, making functional-style code more readable and enabling DSL-like syntax patterns.

<!-- sdn-diagram:id=trailing_blocks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trailing_blocks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trailing_blocks_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trailing_blocks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/trailing_blocks_spec.spl` |
| Updated | 2026-06-01 |
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

1. fn apply
2. f
3. var result = apply
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(x, f):
    f(x)

var result = apply(5) \n: n * 2
expect(result).to_equal(10)
```

</details>

#### works with method-style calls

1. fn double each
2. result push
   - Expected: doubled[0] equals `2`
   - Expected: doubled[1] equals `4`
   - Expected: doubled[2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn fold
2. acc = f
   - Expected: sum equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn fold3
2. acc = f
3. var result = fold3
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn call block
2. block
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn call_block(block):
    block()

var result = call_block \: 42
expect(result).to_equal(42)
```

</details>

#### useful for constant responses

1. fn get handler
2. handler
   - Expected: response equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_handler(path, handler):
    handler()

val response = get_handler("/health") \: "ok"
expect(response).to_equal("ok")
```

</details>

### Trailing Blocks - Expression Forms

#### with inline expressions

#### evaluates inline expression

1. fn transform
2. f
3. var result = transform
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transform(x, f):
    f(x)

var result = transform(10) \n: n + 5
expect(result).to_equal(15)
```

</details>

#### supports arithmetic expressions

1. fn compute
2. op
   - Expected: sum equals `7`
   - Expected: product equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn run block
2. block
3. var result = run block
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_block(block):
    block()

var result = run_block(\: 42)

expect(result).to_equal(42)
```

</details>

#### can compute complex expressions inline

1. fn process
2. handler
3. var result = process
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(x, handler):
    handler(x)

var result = process(5) \n: (n * 2) + 3

expect(result).to_equal(13)
```

</details>

### Trailing Blocks - Call Contexts

#### with parenthesized calls

#### works with regular function calls

1. fn apply twice
2. f
3. var result = apply twice
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply_twice(x, f):
    f(f(x))

var result = apply_twice(3, \n: n + 2)
expect(result).to_equal(7)
```

</details>

#### combines regular args with trailing block

1. fn apply with base
2. base + f
3. var result = apply with base
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply_with_base(base, x, f):
    base + f(x)

var result = apply_with_base(10, 5) \n: n * 2
expect(result).to_equal(20)
```

</details>

#### with no-parentheses calls

#### works without parentheses

1. fn double
2. f
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x, f):
    f(x)

var result = double 7 \n: n * 2
expect(result).to_equal(14)
```

</details>

### Trailing Blocks - Method Chaining

#### with sequential operations

#### chains filter and map operations

1. fn filter list
2. result push
3. fn map list
4. result push
   - Expected: doubled[0] equals `2`
   - Expected: doubled[1] equals `6`
   - Expected: doubled[2] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn create handler
2. var result = handler
   - Expected: result equals `response`
3. create handler
4. create handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn outer
2. fn inner
3. f
   - Expected: final equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn make adder
2. fn add
3. f
4. var result = add10
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
