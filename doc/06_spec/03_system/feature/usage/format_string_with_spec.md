# Format String Instantiation Specification

> Format strings allow defining reusable string patterns with placeholders that are filled in later using the `.with` method. Unlike immediate string interpolation, format patterns use raw strings (`r"..."`) to defer placeholder substitution until explicitly called with a dictionary of values.

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
| Updated | 2026-08-26 |
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
use std.spec.step

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

- replaces single placeholder
   - Expected: result equals `Hello World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces single placeholder")
val fmt = r"Hello {name}!"
val result = fmt.with {"name": "World"}
expect(result).to_equal("Hello World!")
```

</details>

#### with multiple placeholders

#### replaces all placeholders

- replaces all placeholders
   - Expected: result equals `Dear Alice, Welcome! - Bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces all placeholders")
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

- replaces all occurrences of same placeholder
   - Expected: result equals `Echo says: Hello Echo!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces all occurrences of same placeholder")
val fmt = r"{name} says: Hello {name}!"
val result = fmt.with {"name": "Echo"}
expect(result).to_equal("Echo says: Hello Echo!")
```

</details>

### FString.with - Edge Cases

#### with empty format

#### returns unchanged string

- returns unchanged string
   - Expected: result equals `No placeholders here`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns unchanged string")
val fmt = r"No placeholders here"
val result = fmt.with {}
expect(result).to_equal("No placeholders here")
```

</details>

#### with empty dict

#### leaves placeholders unchanged

- leaves placeholders unchanged
   - Expected: result equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves placeholders unchanged")
val fmt = r"Hello {name}!"
val result = fmt.with {}
# Use raw string for expected value to avoid interpolation
val expected = r"Hello {name}!"
expect(result).to_equal(expected)
```

</details>

#### with non-string values

#### converts values to strings

- converts values to strings
   - Expected: result equals `Count: 42, Active: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts values to strings")
val fmt = r"Count: {n}, Active: {flag}"
val result = fmt.with {"n": 42, "flag": true}
expect(result).to_equal("Count: 42, Active: true")
```

</details>

### FString.with - Compile-Time Validation

#### with valid keys

#### accepts matching keys

- accepts matching keys
   - Expected: result equals `Hello Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts matching keys")
val fmt = r"Hello {name}!"
val result = fmt.with {"name": "Alice"}
expect(result).to_equal("Hello Alice!")
```

</details>

#### with tracked variable

#### validates keys for variable formats

- validates keys for variable formats
   - Expected: msg equals `Welcome Bob to Paris`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates keys for variable formats")
val fmt = r"Welcome {user} to {city}"
val msg = fmt.with {"user": "Bob", "city": "Paris"}
expect(msg).to_equal("Welcome Bob to Paris")
```

</details>

### FString.with - Use Cases

#### for email generation

#### generates personalized emails

- generates personalized emails
   - Expected: result equals `Dear Alice, Welcome to Acme Inc!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates personalized emails")
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

- builds URLs from formats
   - Expected: url equals `/api/v2/users/42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds URLs from formats")
val api = r"/api/{version}/users/{id}"
val url = api.with {"version": "v2", "id": "42"}
expect(url).to_equal("/api/v2/users/42")
```

</details>

#### for query building

#### builds queries

- builds queries
   - Expected: sql equals `SELECT * FROM users WHERE id = 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds queries")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42fa94257a7651f4ada8c91600d62e82a0e4629874403cce4e6bd03418449513`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42fa94257a7651f4ada8c91600d62e82a0e4629874403cce4e6bd03418449513`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42fa94257a7651f4ada8c91600d62e82a0e4629874403cce4e6bd03418449513`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/format_string_with_spec.spl
mirror: doc/06_spec/03_system/feature/usage/format_string_with_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/format_string_with_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/format_string_with_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/format_string_with_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces single placeholder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/format_string_with_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces all placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/format_string_with_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces all occurrences of same placeholder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
