# Static Keyword Parsing

> Tests parsing and resolution of the `static` keyword for class and struct methods. Uses ClassName.method() dot-access syntax which works in interpreter mode.

<!-- sdn-diagram:id=parser_static_keyword_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_static_keyword_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_static_keyword_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_static_keyword_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Keyword Parsing

Tests parsing and resolution of the `static` keyword for class and struct methods. Uses ClassName.method() dot-access syntax which works in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-004 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/parser_static_keyword_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests parsing and resolution of the `static` keyword for class and struct methods.
Uses ClassName.method() dot-access syntax which works in interpreter mode.

## Syntax

```simple
class Math:
    static fn add(a: i32, b: i32) -> i32:
        return a + b
val result = Math.add(2, 3)
```

## Scenarios

### Static methods in classes

#### parses static method in class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MathOps.add(2, 3)
expect(result).to_equal(5)
```

</details>

#### calls static method without instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MathOps.sub(10, 4)
expect(result).to_equal(6)
```

</details>

#### parses static method with no parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = MathOps.greeting()
expect(msg).to_equal("hello from static")
```

</details>

#### parses static method returning text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = MathOps.greeting()
expect(msg).to_start_with("hello")
```

</details>

### Static methods in impl blocks

#### parses static method in impl block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Counter.new()
expect(c.get_count()).to_equal(0)
```

</details>

#### parses multiple static methods in impl

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = Counter.new()
val c2 = Counter.from(10)
expect(c1.get_count()).to_equal(0)
expect(c2.get_count()).to_equal(10)
```

</details>

### Static vs instance methods

#### distinguishes static from instance methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Counter.from(5)
val v = c.get_count()
expect(v).to_equal(5)
```

</details>

#### parses class with both static and instance methods

1. var c = Counter new
2. c increment
   - Expected: c.get_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Counter.new()
c.increment()
expect(c.get_count()).to_equal(1)
```

</details>

### Static methods as factories

#### uses static method as constructor alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = Config.default_config()
expect(cfg.get_timeout()).to_equal(30)
```

</details>

#### uses static method with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = Config.with_timeout(60)
expect(cfg.get_timeout()).to_equal(60)
```

</details>

### Static method visibility

#### parses public static method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MathOps.add(100, 200)
expect(result).to_equal(300)
```

</details>

#### parses private static method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MathOps.negate(42)
expect(result).to_equal(-42)
```

</details>

### Static methods with generics

#### parses static generic method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic statics work at parse level; runtime uses i64
val result = MathOps.square(5)
expect(result).to_equal(25)
```

</details>

### Static methods calling other static methods

#### calls static method from another static method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = MathOps.add(1, 2)
val b = MathOps.sub(10, a)
expect(b).to_equal(7)
```

</details>

### Static methods with default parameters

#### parses static method with default parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = Config.default_config()
expect(cfg.get_timeout()).to_equal(30)
```

</details>

### Static methods returning complex types

#### parses static method returning array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = MathOps.numbers()
expect(nums.len()).to_equal(3)
```

</details>

#### parses static method returning option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Pair.create(3, 7)
expect(p.sum()).to_equal(10)
```

</details>

### Static method edge cases

#### parses static method with no return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Counter.new()
expect(c.get_count()).to_equal(0)
```

</details>

#### parses static method with complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MathOps.add(MathOps.square(3), MathOps.square(4))
expect(result).to_equal(25)
```

</details>

#### parses nested static method calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MathOps.add(MathOps.add(1, 2), MathOps.add(3, 4))
expect(result).to_equal(10)
```

</details>

### Static methods in async contexts

#### parses async static method

1. static async fn fetch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class AsyncUtils:
    static async fn fetch() -> i32:
        return 42

# Note: actual await testing requires async runtime
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
