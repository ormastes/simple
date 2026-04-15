# Format String Instantiation Specification

**Feature ID:** #2300-2305 | **Category:** Language | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/usage/format_string_with_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### FString.with - Basic Usage

#### with single placeholder

- ✅ replaces single placeholder
#### with multiple placeholders

- ✅ replaces all placeholders
#### with repeated placeholder

- ✅ replaces all occurrences of same placeholder
### FString.with - Edge Cases

#### with empty format

- ✅ returns unchanged string
#### with empty dict

- ✅ leaves placeholders unchanged
#### with non-string values

- ✅ converts values to strings
### FString.with - Compile-Time Validation

#### with valid keys

- ✅ accepts matching keys
#### with tracked variable

- ✅ validates keys for variable formats
### FString.with - Use Cases

#### for email generation

- ✅ generates personalized emails
#### for URL construction

- ✅ builds URLs from formats
#### for query building

- ✅ builds queries

