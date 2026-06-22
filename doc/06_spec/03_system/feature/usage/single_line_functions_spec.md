# Single-Line Function Definitions Specification

> fn name(): implicit_return_expr

<!-- sdn-diagram:id=single_line_functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=single_line_functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

single_line_functions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=single_line_functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Single-Line Function Definitions Specification

fn name(): implicit_return_expr

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-INLINE |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/single_line_functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
fn name(): implicit_return_expr
fn name(param: Type) -> ReturnType: expr
```

## Key Behaviors

- Single-line functions have an implicit return expression (no explicit `return` needed)
- The expression is evaluated and returned automatically
- Explicit return types are optional but supported
- Works with zero, one, or multiple parameters
- Compatible with class methods and static functions
- Traditional block syntax is still supported and can be mixed in the same file

## Scenarios

### Single-Line Function Definitions

#### basic syntax

#### parses inline expression body

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x): x * 2
expect double(5) == 10
```

</details>

#### parses with multiple parameters

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b): a + b
expect add(3, 4) == 7
```

</details>

#### parses with no parameters

1. fn get answer
2. expect get answer


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_answer(): 42
expect get_answer() == 42
```

</details>

#### handles complex expressions

1. fn complex
2. expect complex


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn complex(x): (x * 2) + (x / 2)
expect complex(10) == 25
```

</details>

#### returns immediately without explicit return

1. fn square
2. expect square


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x): x * x
expect square(4) == 16
```

</details>

#### with explicit return types

#### supports explicit return type annotation

1. fn typed double
2. expect typed double


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn typed_double(x: i64) -> i64: x * 2
expect typed_double(5) == 10
```

</details>

#### works with function parameter types

1. fn typed add
2. expect typed add


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn typed_add(a: i64, b: i64) -> i64: a + b
expect typed_add(10, 20) == 30
```

</details>

#### infers return type from expression

1. fn inferred
2. expect inferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inferred(x): x + 1
expect inferred(41) == 42
```

</details>

#### with method definitions

#### works with class methods

1. fn get count
2. expect c get count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    count: i64

    fn get_count(): self.count

val c = Counter(count: 42)
expect c.get_count() == 42
```

</details>

#### works with mutable methods

1. me add
2. acc add
3. acc add


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Accumulator:
    total: i64

    me add(value: i64):
        self.total = self.total + value

val acc = Accumulator(total: 0)
acc.add(5)
acc.add(10)
expect acc.total == 15
```

</details>

#### works with static functions

1. static fn pi approximation
2. expect MathHelper pi approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class MathHelper:
    static fn pi_approximation(): 3.14159

expect MathHelper.pi_approximation() == 3.14159
```

</details>

#### with collection operations

#### works with lambda-like expressions

1. fn twice each
2. expect twice each


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn twice_each(items: List<i64>): items.map(_ * 2)
expect twice_each([1, 2, 3]) == [2, 4, 6]
```

</details>

#### handles filtering in single line

1. fn evens only
2. expect evens only


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn evens_only(items: List<i64>): items.filter(_ % 2 == 0)
expect evens_only([1, 2, 3, 4, 5]) == [2, 4]
```

</details>

#### mixing with block syntax

#### can coexist with traditional block functions

1. fn inline
2. fn block
3. expect block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inline(x): x * 2
fn block(x):
    val doubled = inline(x)
    doubled + 1
expect block(5) == 11
```

</details>

#### block functions still work normally

1. fn block complex
2. expect block complex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn block_complex(x):
    val y = x * 2
    y + 1
expect block_complex(5) == 11
```

</details>

#### allows either style in same module

1. fn style1
2. fn style2
3. expect style1
4. expect style2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn style1(x): x + 1
fn style2(x):
    x + 2
expect style1(10) == 11
expect style2(10) == 12
```

</details>

#### edge cases

#### works with nested function calls

1. fn inner
2. fn outer
3. inner
4. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inner(x): x + 1
fn outer(x):
    inner(x * 2)
expect outer(5) == 11
```

</details>

#### handles string expressions

1. fn greeting
2. expect greeting


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greeting(name): "Hello, {name}!"
expect greeting("World") == "Hello, World!"
```

</details>

#### works with conditional expressions

1. fn max of two
2. expect max of two
3. expect max of two


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn max_of_two(a, b): if a > b: a else: b
expect max_of_two(10, 5) == 10
expect max_of_two(3, 8) == 8
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
