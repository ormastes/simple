# Format String Instantiation Specification

Format strings allow defining reusable string patterns with placeholders that are filled in later using the `.with` method. Unlike immediate string interpolation, format patterns use raw strings (`r"..."`) to defer placeholder substitution until explicitly called with a dictionary of values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2300-2305 |
| Category | Language |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/format_string_with_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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
val pattern = r"Hello {name}, welcome to {city}!"

val result = pattern.with {"name": "Alice", "city": "Tokyo"}
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
val email_pattern = r"Dear {recipient},\n\n{body}\n\nBest,\n{sender}"
val email = email_pattern.with {
"recipient": "Alice",
"body": "Thank you for your order!",
"sender": "Bob"
}

val api_url = r"https://api.example.com/{version}/users/{user_id}"
val url = api_url.with {"version": "v2", "user_id": "12345"}
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/format_string_with/result.json` |

## Scenarios

- replaces single placeholder
- replaces all placeholders
- replaces all occurrences of same placeholder
- returns unchanged string
- leaves placeholders unchanged
- converts values to strings
- accepts matching keys
- validates keys for variable formats
- generates personalized emails
- builds URLs from formats
- builds queries
