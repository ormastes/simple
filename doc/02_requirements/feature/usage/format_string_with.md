# Format String Instantiation Specification
*Source:* `test/feature/usage/format_string_with_spec.spl`
**Feature IDs:** #2300-2305  |  **Category:** Language  |  **Status:** Implemented

## Overview




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
val email_pattern = r"Dear {recipient},{NL}{NL}{body}{NL}{NL}Best,{NL}{sender}"
val email = email_pattern.with {
    "recipient": "Alice",
    "body": "Thank you for your order!",
    "sender": "Bob"
}

# URL builder
val api_url = r"https://api.example.com/{version}/users/{user_id}"
val url = api_url.with {"version": "v2", "user_id": "12345"}
```

## Feature: FString.with - Basic Usage

## Basic Format Instantiation

    The `.with` method replaces placeholders in a format string
    with values from a dictionary.

### Scenario: with single placeholder

### Scenario: Single Placeholder Replacement

        A format with one placeholder is filled with the corresponding
        dictionary value.

        ```simple
        val fmt = r"Hello {name}!"
        val result = fmt.with {"name": "World"}
        # Result: "Hello World!"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | replaces single placeholder | pass |

**Example:** replaces single placeholder
    Given val fmt = r"Hello {name}!"
    Given val result = fmt.with {"name": "World"}
    Then  expect(result).to_equal("Hello World!")

### Scenario: with multiple placeholders

### Scenario: Multiple Placeholder Replacement

        Formats can contain multiple distinct placeholders, each
        replaced by its corresponding dictionary value.

        ```simple
        val fmt = r"Welcome {user} to {city}!"
        val result = fmt.with {"user": "Alice", "city": "Tokyo"}
        # Result: "Welcome Alice to Tokyo!"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | replaces all placeholders | pass |

**Example:** replaces all placeholders
    Given val greeting = r"Dear {recipient}, {message} - {sender}"
    Given val result = greeting.with {
    Then  expect(result).to_equal("Dear Alice, Welcome! - Bob")

### Scenario: with repeated placeholder

### Scenario: Same Placeholder Multiple Times

        The same placeholder can appear multiple times in a format.
        All occurrences are replaced with the same value.

        ```simple
        val fmt = r"{name} says: Hello {name}!"
        val result = fmt.with {"name": "Echo"}
        # Result: "Echo says: Hello Echo!"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | replaces all occurrences of same placeholder | pass |

**Example:** replaces all occurrences of same placeholder
    Given val fmt = r"{name} says: Hello {name}!"
    Given val result = fmt.with {"name": "Echo"}
    Then  expect(result).to_equal("Echo says: Hello Echo!")

## Feature: FString.with - Edge Cases

## Edge Case Handling

    Tests for boundary conditions and unusual scenarios.

### Scenario: with empty format

### Scenario: No Placeholders

        A format with no placeholders returns the original string.

        ```simple
        val fmt = r"No placeholders here"
        val result = fmt.with {}
        # Result: "No placeholders here"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | returns unchanged string | pass |

**Example:** returns unchanged string
    Given val fmt = r"No placeholders here"
    Given val result = fmt.with {}
    Then  expect(result).to_equal("No placeholders here")

### Scenario: with empty dict

### Scenario: Empty Dictionary

        Calling `.with {}` on a format with placeholders
        leaves the placeholders unchanged.

        ```simple
        val fmt = r"Hello {name}!"
        val result = fmt.with {}
        # Result: "Hello {name}!"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | leaves placeholders unchanged | pass |

**Example:** leaves placeholders unchanged
    Given val fmt = r"Hello {name}!"
    Given val result = fmt.with {}
    Given val expected = r"Hello {name}!"
    Then  expect(result).to_equal(expected)

### Scenario: with non-string values

### Scenario: Non-String Values in Dict

        Dictionary values are converted to strings automatically.

        ```simple
        val fmt = r"Count: {n}, Active: {flag}"
        val result = fmt.with {"n": 42, "flag": true}
        # Result: "Count: 42, Active: true"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | converts values to strings | pass |

**Example:** converts values to strings
    Given val fmt = r"Count: {n}, Active: {flag}"
    Given val result = fmt.with {"n": 42, "flag": true}
    Then  expect(result).to_equal("Count: 42, Active: true")

## Feature: FString.with - Compile-Time Validation

## Compile-Time Key Validation

    The type checker validates that dictionary keys match the
    format placeholders when the format is statically known.

### Scenario: with valid keys

### Scenario: All Keys Match

        When all dictionary keys match placeholders, the code compiles
        and runs successfully.

        ```simple
        val fmt = r"Hello {name}!"
        val result = fmt.with {"name": "Alice"}  # Compiles OK
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | accepts matching keys | pass |

**Example:** accepts matching keys
    Given val fmt = r"Hello {name}!"
    Given val result = fmt.with {"name": "Alice"}
    Then  expect(result).to_equal("Hello Alice!")

### Scenario: with tracked variable

### Scenario: Variable-Based Format

        Formats stored in variables are tracked for compile-time
        validation.

        ```simple
        val fmt = r"Welcome {user} to {city}"
        val msg = fmt.with {"user": "Bob", "city": "Paris"}
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | validates keys for variable formats | pass |

**Example:** validates keys for variable formats
    Given val fmt = r"Welcome {user} to {city}"
    Given val msg = fmt.with {"user": "Bob", "city": "Paris"}
    Then  expect(msg).to_equal("Welcome Bob to Paris")

## Feature: FString.with - Use Cases

## Practical Applications

    Common patterns for using format string instantiation.

### Scenario: for email generation

### Scenario: Email Generation

        Format strings are ideal for generating emails with variable content.

        ```simple
        val email_fmt = r"Dear {name}, Welcome to {company}!"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | generates personalized emails | pass |

**Example:** generates personalized emails
    Given val email_fmt = r"Dear {name}, Welcome to {company}!"
    Given val result = email_fmt.with {
    Then  expect(result).to_equal("Dear Alice, Welcome to Acme Inc!")

### Scenario: for URL construction

### Scenario: Dynamic URL Building

        Build URLs with variable path segments and query parameters.

        ```simple
        val api = r"/api/{version}/users/{id}"
        val url = api.with {"version": "v2", "id": "42"}
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | builds URLs from formats | pass |

**Example:** builds URLs from formats
    Given val api = r"/api/{version}/users/{id}"
    Given val url = api.with {"version": "v2", "id": "42"}
    Then  expect(url).to_equal("/api/v2/users/42")

### Scenario: for query building

### Scenario: Query Pattern

        Build parameterized queries (note: use proper escaping in production).

        ```simple
        val query = r"SELECT * FROM {table} WHERE id = {id}"
        val sql = query.with {"table": "users", "id": "42"}
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | builds queries | pass |

**Example:** builds queries
    Given val query = r"SELECT * FROM {table} WHERE id = {id}"
    Given val sql = query.with {"table": "users", "id": "42"}
    Then  expect(sql).to_equal("SELECT * FROM users WHERE id = 42")


