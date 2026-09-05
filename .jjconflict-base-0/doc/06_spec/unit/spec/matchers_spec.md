# Matchers Specification

> Tests covering BDD Matchers.

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

- creates a successful match result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a successful match result")
val result = MatchResult.success()
expect(result.matched).to eq(true)
expect(result.is_success()).to eq(true)
expect(result.is_failure()).to eq(false)
```

</details>

#### creates a failure match result

- creates a failure match result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a failure match result")
val result = MatchResult.failure("error message")
expect(result.matched).to eq(false)
expect(result.is_success()).to eq(false)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to eq("error message")
```

</details>

#### can create with custom messages

- can create with custom messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can create with custom messages")
val result = MatchResult.new(false, "fail msg", "negated fail msg")
expect(result.failure_message).to eq("fail msg")
expect(result.negated_failure_message).to eq("negated fail msg")
```

</details>

#### has_failure_message returns true when message is set

- has_failure_message returns true when message is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_failure_message returns true when message is set")
val result = MatchResult.failure("error")
expect(result.has_failure_message()).to eq(true)
```

</details>

#### has_failure_message returns false for empty message

- has_failure_message returns false for empty message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_failure_message returns false for empty message")
val result = MatchResult.success()
expect(result.has_failure_message()).to eq(false)
```

</details>

#### get_message returns appropriate message based on negation

- get_message returns appropriate message based on negation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_message returns appropriate message based on negation")
val result = MatchResult.new(false, "fail", "negated fail")
expect(result.get_message(false)).to eq("fail")
expect(result.get_message(true)).to eq("negated fail")
```

</details>

#### with_failure_message creates new result with updated message

- with_failure_message creates new result with updated message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_failure_message creates new result with updated message")
val result = MatchResult.success().with_failure_message("new fail")
expect(result.failure_message).to eq("new fail")
```

</details>

#### with_negated_message creates new result with updated negated message

- with_negated_message creates new result with updated negated message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_negated_message creates new result with updated negated message")
val result = MatchResult.success().with_negated_message("new negated")
expect(result.negated_failure_message).to eq("new negated")
```

</details>

#### negate inverts the match result

- negate inverts the match result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negate inverts the match result")
val result = MatchResult.success().negate()
expect(result.matched).to eq(false)
```

</details>

#### summary provides readable description

- summary provides readable description


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("summary provides readable description")
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

- matches equal integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches equal integers")
val matcher = eq(42)
val result = matcher.matches(42)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for unequal integers

- fails for unequal integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for unequal integers")
val matcher = eq(42)
val result = matcher.matches(10)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Expected")
```

</details>

#### matches equal strings

- matches equal strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches equal strings")
val matcher = eq("hello")
val result = matcher.matches("hello")
expect(result.is_success()).to eq(true)
```

</details>

#### fails for unequal strings

- fails for unequal strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for unequal strings")
val matcher = eq("hello")
val result = matcher.matches("world")
expect(result.is_failure()).to eq(true)
```

</details>

#### Core Matchers - be

#### matches identical values (identity check)

- matches identical values (identity check)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches identical values (identity check)")
val obj = [1, 2, 3]
val matcher = be(obj)
val result = matcher.matches(obj)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for different objects with same value

- fails for different objects with same value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for different objects with same value")
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

- matches None value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches None value")
val matcher = be_nil()
val result = matcher.matches(None)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for Some value

- fails for Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for Some value")
val matcher = be_nil()
val result = matcher.matches(Some(42))
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Expected None")
```

</details>

#### Comparison Matchers - gt

#### matches when actual > expected

- matches when actual > expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when actual > expected")
val matcher = gt(5)
val result = matcher.matches(10)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual <= expected

- fails when actual <= expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when actual <= expected")
val matcher = gt(5)
val result = matcher.matches(3)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("greater than")
```

</details>

#### Comparison Matchers - lt

#### matches when actual < expected

- matches when actual < expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when actual < expected")
val matcher = lt(10)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual >= expected

- fails when actual >= expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when actual >= expected")
val matcher = lt(5)
val result = matcher.matches(10)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("less than")
```

</details>

#### Comparison Matchers - gte

#### matches when actual > expected

- matches when actual > expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when actual > expected")
val matcher = gte(5)
val result = matcher.matches(10)
expect(result.is_success()).to eq(true)
```

</details>

#### matches when actual == expected

- matches when actual == expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when actual == expected")
val matcher = gte(5)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual < expected

- fails when actual < expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when actual < expected")
val matcher = gte(10)
val result = matcher.matches(5)
expect(result.is_failure()).to eq(true)
```

</details>

#### Comparison Matchers - lte

#### matches when actual < expected

- matches when actual < expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when actual < expected")
val matcher = lte(10)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### matches when actual == expected

- matches when actual == expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when actual == expected")
val matcher = lte(5)
val result = matcher.matches(5)
expect(result.is_success()).to eq(true)
```

</details>

#### fails when actual > expected

- fails when actual > expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when actual > expected")
val matcher = lte(5)
val result = matcher.matches(10)
expect(result.is_failure()).to eq(true)
```

</details>

#### Collection Matchers - include

#### matches when array contains element

- matches when array contains element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when array contains element")
val matcher = include(2)
val result = matcher.matches([1, 2, 3])
expect(result.is_success()).to eq(true)
```

</details>

#### fails when array does not contain element

- fails when array does not contain element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when array does not contain element")
val matcher = include(5)
val result = matcher.matches([1, 2, 3])
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("include")
```

</details>

#### Collection Matchers - be_empty

#### matches empty array

- matches empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches empty array")
val matcher = be_empty()
val result = matcher.matches([])
expect(result.is_success()).to eq(true)
```

</details>

#### fails for non-empty array

- fails for non-empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for non-empty array")
val matcher = be_empty()
val result = matcher.matches([1, 2, 3])
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("empty")
```

</details>

#### Collection Matchers - have_length

#### matches when length equals expected

- matches when length equals expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when length equals expected")
val matcher = have_length(3)
val result = matcher.matches([1, 2, 3])
expect(result.is_success()).to eq(true)
```

</details>

#### fails when length does not match

- fails when length does not match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when length does not match")
val matcher = have_length(5)
val result = matcher.matches([1, 2, 3])
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("length")
```

</details>

#### Collection Matchers - have_size

#### is an alias for have_length

- is an alias for have_length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is an alias for have_length")
val matcher = have_size(2)
val result = matcher.matches([1, 2])
expect(result.is_success()).to eq(true)
```

</details>

#### Boolean Matchers - be_true

#### matches true value

- matches true value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches true value")
val matcher = be_true()
val result = matcher.matches(true)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for false value

- fails for false value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for false value")
val matcher = be_true()
val result = matcher.matches(false)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("true")
```

</details>

#### Boolean Matchers - be_false

#### matches false value

- matches false value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches false value")
val matcher = be_false()
val result = matcher.matches(false)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for true value

- fails for true value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for true value")
val matcher = be_false()
val result = matcher.matches(true)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("false")
```

</details>

#### Boolean Matchers - be_truthy

#### matches Some value

- matches Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Some value")
val matcher = be_truthy()
val result = matcher.matches(Some(42))
expect(result.is_success()).to eq(true)
```

</details>

#### fails for None value

- fails for None value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for None value")
val matcher = be_truthy()
val result = matcher.matches(None)
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("Some")
```

</details>

#### Boolean Matchers - be_falsy

#### matches None value

- matches None value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches None value")
val matcher = be_falsy()
val result = matcher.matches(None)
expect(result.is_success()).to eq(true)
```

</details>

#### fails for Some value

- fails for Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for Some value")
val matcher = be_falsy()
val result = matcher.matches(Some(42))
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("None")
```

</details>

#### String Matchers - include_string

#### matches when string contains substring

- matches when string contains substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when string contains substring")
val matcher = include_string("world")
val result = matcher.matches("hello world")
expect(result.is_success()).to eq(true)
```

</details>

#### fails when string does not contain substring

- fails when string does not contain substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when string does not contain substring")
val matcher = include_string("foo")
val result = matcher.matches("hello world")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("include")
```

</details>

#### String Matchers - start_with

#### matches when string starts with prefix

- matches when string starts with prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when string starts with prefix")
val matcher = start_with("hello")
val result = matcher.matches("hello world")
expect(result.is_success()).to eq(true)
```

</details>

#### fails when string does not start with prefix

- fails when string does not start with prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when string does not start with prefix")
val matcher = start_with("world")
val result = matcher.matches("hello world")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("start with")
```

</details>

#### String Matchers - end_with

#### matches when string ends with suffix

- matches when string ends with suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when string ends with suffix")
val matcher = end_with("world")
val result = matcher.matches("hello world")
expect(result.is_success()).to eq(true)
```

</details>

#### fails when string does not end with suffix

- fails when string does not end with suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when string does not end with suffix")
val matcher = end_with("hello")
val result = matcher.matches("hello world")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("end with")
```

</details>

#### String Matchers - be_blank

#### matches empty string

- matches empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches empty string")
val matcher = be_blank()
val result = matcher.matches("")
expect(result.is_success()).to eq(true)
```

</details>

#### matches whitespace-only string

- matches whitespace-only string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches whitespace-only string")
val matcher = be_blank()
val result = matcher.matches("   ")
expect(result.is_success()).to eq(true)
```

</details>

#### fails for non-blank string

- fails for non-blank string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for non-blank string")
val matcher = be_blank()
val result = matcher.matches("hello")
expect(result.is_failure()).to eq(true)
expect(result.failure_message).to include_string("blank")
```

</details>

#### Type Matchers - be_option

#### matches Option type (Some)

- matches Option type (Some)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Option type (Some)")
val matcher = be_option()
val result = matcher.matches(Some(42))
expect(result.is_success()).to eq(true)
```

</details>

#### matches Option type (None)

- matches Option type (None)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Option type (None)")
val matcher = be_option()
val result = matcher.matches(None)
expect(result.is_success()).to eq(true)
```

</details>

#### Type Matchers - be_result

#### matches Result type (Ok)

- matches Result type (Ok)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Result type (Ok)")
val matcher = be_result()
val result = matcher.matches(Ok(42))
expect(result.is_success()).to eq(true)
```

</details>

#### matches Result type (Err)

- matches Result type (Err)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Result type (Err)")
val matcher = be_result()
val result = matcher.matches(Err("error"))
expect(result.is_success()).to eq(true)
```

</details>

#### Type Matchers - be_instance_of

#### creates a matcher for type checking

- creates a matcher for type checking


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a matcher for type checking")
val matcher = be_instance_of("String")
# Actual type checking depends on interpreter support
# This test verifies the matcher can be created
expect(matcher.type_name).to eq("type")
```

</details>

#### Type Matchers - be_a and be_an

#### be_a is an alias for be_instance_of

- be_a is an alias for be_instance_of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("be_a is an alias for be_instance_of")
val matcher = be_a("Array")
expect(matcher.type_name).to eq("Array")
```

</details>

#### be_an is an alias for be_instance_of

- be_an is an alias for be_instance_of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("be_an is an alias for be_instance_of")
val matcher = be_an("Option")
expect(matcher.type_name).to eq("Option")
```

</details>

#### Error Matchers - raise_error

#### creates an error matcher with type

- creates an error matcher with type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an error matcher with type")
val matcher = raise_error(Some(ValueError), None)
# Error matching depends on exception support
# This verifies the matcher can be created
expect(matcher.expected_type.is_some()).to eq(true)
```

</details>

#### creates an error matcher with message

- creates an error matcher with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an error matcher with message")
val matcher = raise_error(None, Some("error message"))
expect(matcher.expected_message).to eq(Some("error message"))
```

</details>

#### matches when error is provided

- matches when error is provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches when error is provided")
val matcher = raise_error(None, None)
val error = Error { type: "TestError", message: "test" }
val result = matcher.matches(Some(error))
expect(result.is_success()).to eq(true)
```

</details>

#### fails when no error is provided

- fails when no error is provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when no error is provided")
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
| Source | `test/unit/spec/matchers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BDD Matchers.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbb22c62c4871b76dae19a4ee355f7f846e0ed5ec222b67687d41702a65c2bee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbb22c62c4871b76dae19a4ee355f7f846e0ed5ec222b67687d41702a65c2bee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbb22c62c4871b76dae19a4ee355f7f846e0ed5ec222b67687d41702a65c2bee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/spec/matchers_spec.spl
mirror: doc/06_spec/unit/spec/matchers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/spec/matchers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/spec/matchers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/spec/matchers_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a successful match result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/matchers_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a failure match result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/matchers_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can create with custom messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/matchers_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can create with custom messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
