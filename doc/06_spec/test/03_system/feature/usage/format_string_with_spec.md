# Format String Instantiation Specification

> Format strings allow defining reusable string patterns with placeholders that are filled in later using the `.with` method. Unlike immediate string interpolation, format patterns use raw strings (`r"..."`) to defer placeholder substitution until explicitly called with a dictionary of values.

<!-- sdn-diagram:id=format_string_with_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=format_string_with_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

format_string_with_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=format_string_with_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Format String Instantiation Specification

Format strings allow defining reusable string patterns with placeholders that are filled in later using the `.with` method. Unlike immediate string interpolation, format patterns use raw strings (`r"..."`) to defer placeholder substitution until explicitly called with a dictionary of values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2300-2305 |
| Category | Language |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/format_string_with_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Format strings allow defining reusable string patterns with placeholders
that are filled in later using the `.with` method. Unlike immediate string
interpolation, format patterns use raw strings (`r"..."`) to defer placeholder
substitution until explicitly called with a dictionary of values.

This enables:
- Compile-time validation of dictionary keys against format placeholders
- Separation of format definition from data binding
- Type-safe string formatting with clear error messages

## Syntax

```simple
# Define a format pattern with raw string (no immediate interpolation)
val pattern = r"Hello {name}, welcome to {city}!"

# Instantiate with .with and a dictionary (no parentheses needed)
val result = pattern.with {"name": "Alice", "city": "Tokyo"}
# Result: "Hello Alice, welcome to Tokyo!"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Raw String | `r"..."` syntax prevents immediate interpolation |
| Placeholder | `{key}` marks where values will be inserted |
| .with Method | Replaces placeholders with dictionary values |
| Compile-time Validation | Type checker ensures dict keys match placeholders |

## Behavior

- Raw strings preserve `{placeholder}` syntax without evaluating
- `.with` accepts a dictionary with string keys and any values
- Placeholders not in dict remain unchanged (partial application)
- Extra dict keys are ignored at runtime (but caught at compile-time)
- Type checker validates keys match when format is statically known

## Related Specifications

- [String Interpolation](../string_interpolation/string_interpolation_spec.spl) - Immediate interpolation
- [Dictionary Types](../dictionary_types/dictionary_types_spec.spl) - Dict syntax and operations
- [Type Inference](../type_inference/type_inference_spec.spl) - Const key validation

## Implementation Notes

The type checker tracks FString placeholders as `const_keys` metadata.
When `.with` is called on a tracked FString variable, the dict argument
is validated against the expected keys at compile time.

Runtime implementation performs simple string replacement for each key-value pair.

## Examples

```simple
# Email pattern
val email_pattern = r"Dear {recipient},\n\n{body}\n\nBest,\n{sender}"
val email = email_pattern.with {
"recipient": "Alice",
"body": "Thank you for your order!",
"sender": "Bob"
}

# URL builder
val api_url = r"https://api.example.com/{version}/users/{user_id}"
val url = api_url.with {"version": "v2", "user_id": "12345"}
```

## Scenarios

### FString.with - Basic Usage

#### with single placeholder

#### replaces single placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"Hello {name}!"
val result = fmt.with {"name": "World"}
expect(result).to_equal("Hello World!")
```

</details>

#### with multiple placeholders

#### replaces all placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val greeting = r"Dear {recipient}, {message} - {sender}"
val result = greeting.with {
    "recipient": "Alice",
    "message": "Welcome!",
    "sender": "Bob"
}
expect(result).to_equal("Dear Alice, Welcome! - Bob")
```

</details>

#### with repeated placeholder

#### replaces all occurrences of same placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"{name} says: Hello {name}!"
val result = fmt.with {"name": "Echo"}
expect(result).to_equal("Echo says: Hello Echo!")
```

</details>

### FString.with - Edge Cases

#### with empty format

#### returns unchanged string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"No placeholders here"
val result = fmt.with {}
expect(result).to_equal("No placeholders here")
```

</details>

#### with empty dict

#### leaves placeholders unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"Hello {name}!"
val result = fmt.with {}
# Use raw string for expected value to avoid interpolation
val expected = r"Hello {name}!"
expect(result).to_equal(expected)
```

</details>

#### with non-string values

#### converts values to strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"Count: {n}, Active: {flag}"
val result = fmt.with {"n": 42, "flag": true}
expect(result).to_equal("Count: 42, Active: true")
```

</details>

### FString.with - Compile-Time Validation

#### with valid keys

#### accepts matching keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"Hello {name}!"
val result = fmt.with {"name": "Alice"}
expect(result).to_equal("Hello Alice!")
```

</details>

#### with tracked variable

#### validates keys for variable formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = r"Welcome {user} to {city}"
val msg = fmt.with {"user": "Bob", "city": "Paris"}
expect(msg).to_equal("Welcome Bob to Paris")
```

</details>

### FString.with - Use Cases

#### for email generation

#### generates personalized emails

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val email_fmt = r"Dear {name}, Welcome to {company}!"
val result = email_fmt.with {
    "name": "Alice",
    "company": "Acme Inc"
}
expect(result).to_equal("Dear Alice, Welcome to Acme Inc!")
```

</details>

#### for URL construction

#### builds URLs from formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val api = r"/api/{version}/users/{id}"
val url = api.with {"version": "v2", "id": "42"}
expect(url).to_equal("/api/v2/users/42")
```

</details>

#### for query building

#### builds queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = r"SELECT * FROM {table} WHERE id = {id}"
val sql = query.with {"table": "users", "id": "42"}
expect(sql).to_equal("SELECT * FROM users WHERE id = 42")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
