# Matchers Specification

> <details>

<!-- sdn-diagram:id=matchers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=matchers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

matchers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=matchers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 63 | 63 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Matchers Specification

## Scenarios

### BDD Matchers

#### MatchResult

#### creates a successful match result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.success()
expect(result.matched).to eq(true)
expect(result.is_success()).to eq(true)
expect(result.is_failure()).to eq(false)
```

</details>

#### creates a failure match result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.failure("error message")
expect(result.matched).to eq(false)
expect(result.is_success()).to eq(false)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to eq("error message")
```

</details>

#### can create with custom messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.new(false, "fail msg", "negated fail msg")
expect(result.failure_message).to eq("fail msg")
expect(result.negated_failure_message).to eq("negated fail msg")
```

</details>

#### has_failure_message returns true when message is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.failure("error")
expect(result.has_failure_message()).to eq(true)
```

</details>

#### has_failure_message returns false for empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.success()
expect(result.has_failure_message()).to eq(false)
```

</details>

#### get_message returns appropriate message based on negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.new(false, "fail", "negated fail")
expect(result.get_message(false)).to eq("fail")
expect(result.get_message(true)).to eq("negated fail")
```

</details>

#### with_failure_message creates new result with updated message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.success().with_failure_message("new fail")
expect(result.failure_message).to eq("new fail")
```

</details>

#### with_negated_message creates new result with updated negated message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.success().with_negated_message("new negated")
expect(result.negated_failure_message).to eq("new negated")
```

</details>

#### negate inverts the match result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MatchResult.success().negate()
expect(result.matched).to eq(false)
```

</details>

#### summary provides readable description

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = MatchResult.success()
expect(success.summary()).to include_string("success")

val failure = MatchResult.failure("test error")
val summary = failure.summary()
expect(summary).to include_string("failure")
expect(summary).to include_string("test error")
```

</details>

#### Core Matchers - eq

#### matches equal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = eq(42)
val result = matcher.matches(42)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for unequal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = eq(42)
val result = matcher.matches(10)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Expected")
```

</details>

#### matches equal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = eq("hello")
val result = matcher.matches("hello")
expect(result.is_success()).to eq(true)
```

</details>

#### fails for unequal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = eq("hello")
val result = matcher.matches("world")
expect(result.is_failure()).to eq(true)
```

</details>

#### Core Matchers - be

#### matches identical values (identity check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = [1, 2, 3]
val matcher = be(obj)
val result = matcher.matches(obj)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for different objects with same value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj1 = [1, 2, 3]
val obj2 = [1, 2, 3]
val matcher = be(obj1)
val result = matcher.matches(obj2)
# Identity check - different objects
expect(result.is_failure()).to eq(true)
```

</details>

#### Core Matchers - be_nil

#### matches None value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_nil()
val result = matcher.matches(None)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_nil()
val result = matcher.matches(Some(42))
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Expected None")
```

</details>

#### Comparison Matchers - gt

#### matches when actual > expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = gt(5)
val result = matcher.matches(10)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual <= expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = gt(5)
val result = matcher.matches(3)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("greater than")
```

</details>

#### Comparison Matchers - lt

#### matches when actual < expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = lt(10)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual >= expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = lt(5)
val result = matcher.matches(10)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("less than")
```

</details>

#### Comparison Matchers - gte

#### matches when actual > expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = gte(5)
val result = matcher.matches(10)
expect(result.is_success()).to eq(true)
```

</details>

#### matches when actual == expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = gte(5)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual < expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = gte(10)
val result = matcher.matches(5)
expect(result.is_failure()).to eq(true)
```

</details>

#### Comparison Matchers - lte

#### matches when actual < expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = lte(10)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### matches when actual == expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = lte(5)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual > expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = lte(5)
val result = matcher.matches(10)
expect(result.is_failure()).to eq(true)
```

</details>

#### Collection Matchers - include

#### matches when array contains element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = include(2)
val result = matcher.matches([1, 2, 3])
expect(result.is_success()).to eq(true)
```

</details>

#### fails when array does not contain element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = include(5)
val result = matcher.matches([1, 2, 3])
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("include")
```

</details>

#### Collection Matchers - be_empty

#### matches empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_empty()
val result = matcher.matches([])
expect(result.is_success()).to eq(true)
```

</details>

#### fails for non-empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_empty()
val result = matcher.matches([1, 2, 3])
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("empty")
```

</details>

#### Collection Matchers - have_length

#### matches when length equals expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = have_length(3)
val result = matcher.matches([1, 2, 3])
expect(result.is_success()).to eq(true)
```

</details>

#### fails when length does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = have_length(5)
val result = matcher.matches([1, 2, 3])
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("length")
```

</details>

#### Collection Matchers - have_size

#### is an alias for have_length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = have_size(2)
val result = matcher.matches([1, 2])
expect(result.is_success()).to eq(true)
```

</details>

#### Boolean Matchers - be_true

#### matches true value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_true()
val result = matcher.matches(true)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for false value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_true()
val result = matcher.matches(false)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("true")
```

</details>

#### Boolean Matchers - be_false

#### matches false value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_false()
val result = matcher.matches(false)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for true value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_false()
val result = matcher.matches(true)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("false")
```

</details>

#### Boolean Matchers - be_truthy

#### matches Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_truthy()
val result = matcher.matches(Some(42))
expect(result.is_success()).to eq(true)
```

</details>

#### fails for None value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_truthy()
val result = matcher.matches(None)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Some")
```

</details>

#### Boolean Matchers - be_falsy

#### matches None value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_falsy()
val result = matcher.matches(None)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_falsy()
val result = matcher.matches(Some(42))
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("None")
```

</details>

#### String Matchers - include_string

#### matches when string contains substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = include_string("world")
val result = matcher.matches("hello world")
expect(result.is_success()).to eq(true)
```

</details>

#### fails when string does not contain substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = include_string("foo")
val result = matcher.matches("hello world")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("include")
```

</details>

#### String Matchers - start_with

#### matches when string starts with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = start_with("hello")
val result = matcher.matches("hello world")
expect(result.is_success()).to eq(true)
```

</details>

#### fails when string does not start with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = start_with("world")
val result = matcher.matches("hello world")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("start with")
```

</details>

#### String Matchers - end_with

#### matches when string ends with suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = end_with("world")
val result = matcher.matches("hello world")
expect(result.is_success()).to eq(true)
```

</details>

#### fails when string does not end with suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = end_with("hello")
val result = matcher.matches("hello world")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("end with")
```

</details>

#### String Matchers - be_blank

#### matches empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_blank()
val result = matcher.matches("")
expect(result.is_success()).to eq(true)
```

</details>

#### matches whitespace-only string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_blank()
val result = matcher.matches("   ")
expect(result.is_success()).to eq(true)
```

</details>

#### fails for non-blank string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_blank()
val result = matcher.matches("hello")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("blank")
```

</details>

#### Type Matchers - be_option

#### matches Option type (Some)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_option()
val result = matcher.matches(Some(42))
expect(result.is_success()).to eq(true)
```

</details>

#### matches Option type (None)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_option()
val result = matcher.matches(None)
expect(result.is_success()).to eq(true)
```

</details>

#### Type Matchers - be_result

#### matches Result type (Ok)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_result()
val result = matcher.matches(Ok(42))
expect(result.is_success()).to eq(true)
```

</details>

#### matches Result type (Err)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_result()
val result = matcher.matches(Err("error"))
expect(result.is_success()).to eq(true)
```

</details>

#### Type Matchers - be_instance_of

#### creates a matcher for type checking

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_instance_of("String")
# Actual type checking depends on interpreter support
# This test verifies the matcher can be created
expect(matcher.type_name).to eq("type")
```

</details>

#### Type Matchers - be_a and be_an

#### be_a is an alias for be_instance_of

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_a("Array")
expect(matcher.type_name).to eq("Array")
```

</details>

#### be_an is an alias for be_instance_of

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = be_an("Option")
expect(matcher.type_name).to eq("Option")
```

</details>

#### Error Matchers - raise_error

#### creates an error matcher with type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = raise_error(Some(ValueError), None)
# Error matching depends on exception support
# This verifies the matcher can be created
expect(matcher.expected_type.is_some()).to eq(true)
```

</details>

#### creates an error matcher with message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = raise_error(None, Some("error message"))
expect(matcher.expected_message).to eq(Some("error message"))
```

</details>

#### matches when error is provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = raise_error(None, None)
val error = Error { type: "TestError", message: "test" }
val result = matcher.matches(Some(error))
expect(result.is_success()).to eq(true)
```

</details>

#### fails when no error is provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = raise_error(None, None)
val result = matcher.matches(None)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Expected an error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/matchers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BDD Matchers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 63 |
| Active scenarios | 63 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
