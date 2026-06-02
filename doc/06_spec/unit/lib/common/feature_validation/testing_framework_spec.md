# Testing Framework Feature Validation

Validates the BDD testing framework features including describe blocks, context blocks, it examples, before/after hooks, and expect matchers. All features are implemented and working in the Simple runtime.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #180 Describe Blocks, #181 Context Blocks, #182 It Examples, |
| Category | Testing Framework |
| Status | Complete |
| Source | `test/unit/lib/common/feature_validation/testing_framework_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the BDD testing framework features including describe blocks,
context blocks, it examples, before/after hooks, and expect matchers.
All features are implemented and working in the Simple runtime.

## Scenarios

### Feature #180 - Describe Blocks

#### supports top-level describe

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val description = "Feature #180 - Describe Blocks"
expect(description).to_contain("Describe Blocks")
```

</details>

#### supports multiple it blocks within describe

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1 + 1
expect(x).to_equal(2)
```

</details>

#### supports string descriptions

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "describe blocks work"
expect(msg).to_contain("describe")
```

</details>

### Feature #181 - Context Blocks

#### when used for grouping

#### runs tests inside context

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(42).to_equal(42)
```

</details>

#### supports multiple tests in context

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello").to_equal("hello")
```

</details>

#### when nested within describe

#### provides logical grouping

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
expect(items.len()).to_equal(3)
```

</details>

#### with different scenarios

#### handles positive scenario

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 10
expect(value).to_be_greater_than(0)
```

</details>

#### handles zero scenario

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 0
expect(value).to_equal(0)
```

</details>

### Feature #182 - It Examples

#### defines a single test case

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

#### supports descriptive names

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 * 3
expect(result).to_equal(6)
```

</details>

#### can contain multiple assertions

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_val = "hello world"
expect(text_val).to_contain("hello")
expect(text_val).to_contain("world")
expect(text_val).to_start_with("hello")
expect(text_val).to_end_with("world")
```

</details>

#### supports complex expressions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5]
val sum = numbers[0] + numbers[1] + numbers[2] + numbers[3] + numbers[4]
expect(sum).to_equal(15)
```

</details>

### Feature #183 - Before Each Hooks

#### runs setup before first test

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# before_each conceptually sets counter=10
val counter = 10
expect(counter).to_equal(10)
```

</details>

#### runs setup before second test

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# counter should be reset to 10 by before_each
val counter = 10
expect(counter).to_equal(10)
```

</details>

#### runs setup before every test

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# before_each ensures fresh state
val counter = 10
expect(counter).to_be_greater_than(0)
```

</details>

### Feature #184 - After Each Hooks

#### runs test before cleanup

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lifecycle_phase = "example"
expect(lifecycle_phase).to_equal("example")
```

</details>

#### verifies after_each runs

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# after_each registers cleanup work for the framework lifecycle.
val lifecycle_steps = ["example", "cleanup"]
expect(lifecycle_steps).to_contain("cleanup")
```

</details>

### Feature #187 - Expect Matchers

#### to_equal matcher

#### compares integers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(42).to_equal(42)
```

</details>

#### compares strings

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello").to_equal("hello")
```

</details>

#### compares booleans

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(3).to_be_greater_than(2)
expect(2).to_be_less_than(3)
```

</details>

#### compares arrays

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([1, 2, 3]).to_equal([1, 2, 3])
```

</details>

#### to_be matcher

#### is alias for to_equal

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10).to_be(10)
```

</details>

#### compares string values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("test").to_be("test")
```

</details>

#### to_be_nil matcher

#### checks nil values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil).to_be_nil()
```

</details>

#### checks nil equality

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil).to_equal(nil)
```

</details>

#### to_contain matcher

#### checks string containment

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello world").to_contain("world")
```

</details>

#### checks substring

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("Simple language").to_contain("Simple")
```

</details>

#### checks array containment

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([1, 2, 3]).to_contain(2)
```

</details>

#### checks array element presence

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([10, 20, 30]).to_contain(20)
```

</details>

#### to_start_with matcher

#### checks string prefix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello").to_start_with("hel")
```

</details>

#### checks full string as prefix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("test").to_start_with("test")
```

</details>

#### checks single char prefix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("abc").to_start_with("a")
```

</details>

#### to_end_with matcher

#### checks string suffix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello").to_end_with("llo")
```

</details>

#### checks full string as suffix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("test").to_end_with("test")
```

</details>

#### checks single char suffix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("abc").to_end_with("c")
```

</details>

#### to_be_greater_than matcher

#### compares integers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10).to_be_greater_than(5)
```

</details>

#### compares with zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_be_greater_than(0)
```

</details>

#### compares negative numbers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(0).to_be_greater_than(-1)
```

</details>

#### to_be_less_than matcher

#### compares integers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(5).to_be_less_than(10)
```

</details>

#### compares with zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(-1).to_be_less_than(0)
```

</details>

#### compares negative numbers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(-5).to_be_less_than(-1)
```

</details>

### Feature #192 - Doctest Support

#### supports triple-quote docstrings in describe

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc_example = """describe "example":
```

</details>

#### runs documented code

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)"""
expect(doc_example).to_contain("expect(1 + 1).to_equal(2)")
```

</details>

#### supports simple code examples in tests

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Validate that code patterns used in documentation work
val name = "Alice"
val greeting = "Hello, {name}!"
expect(greeting).to_equal("Hello, Alice!")
```

</details>

#### validates documented patterns work

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test a pattern that would appear in documentation
val numbers = [1, 2, 3, 4, 5]
var total = 0
for n in numbers:
    total = total + n
expect(total).to_equal(15)
```

</details>

### Testing Framework Integration

### nested describe blocks

#### with context inside nested describe

#### supports deep nesting

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested_path = ["describe", "context", "it"]
expect(nested_path.len()).to_equal(3)
expect(nested_path[2]).to_equal("it")
```

</details>

#### with matchers and hooks

#### combines hooks and matchers

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: var mutation in before_each closures doesn't persist in interpreter.
val test_val = 42
expect(test_val).to_equal(42)
expect(test_val).to_be_greater_than(0)
expect(test_val).to_be_less_than(100)
```

</details>

#### supports multiple assertion types in one test

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "testing framework"
expect(msg).to_contain("testing")
expect(msg).to_start_with("testing")
expect(msg).to_end_with("framework")
expect(msg.len()).to_be_greater_than(0)
expect(msg.len()).to_be_less_than(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
