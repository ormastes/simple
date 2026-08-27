# String Interpolation Specification

> String interpolation allows embedding expressions directly in string literals using curly braces. Simple treats interpolation as the default for regular strings, with raw strings available when needed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Interpolation Specification

String interpolation allows embedding expressions directly in string literals using curly braces. Simple treats interpolation as the default for regular strings, with raw strings available when needed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-001 to #INTERP-020 |
| Category | Language \| Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/string_interpolation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

String interpolation allows embedding expressions directly in string literals
using curly braces. Simple treats interpolation as the default for regular
strings, with raw strings available when needed.

## Syntax

```simple
# Default interpolation (no special prefix needed)
use std.spec.step

val name = "Alice"
print "Hello, {name}!"          # Output: Hello, Alice!

# Expressions in braces
print "Result: {2 + 3}"         # Output: Result: 5

# Raw strings (no interpolation)
val regex = r"pattern: \d+"     # Backslashes not escaped, no interpolation
```

## Key Concepts

| Concept | Syntax | Escaping | Interpolation |
|---------|--------|----------|---------------|
| Default String | `"..."` | Standard | Yes |
| Raw String | `r"..."` | None | No |
| Expression | `{expr}` | Within braces | Yes |
| Escape Sequence | `\n, \t, \\` | Standard | Processed |

## Behavior

- Expressions in braces are evaluated at runtime
- Any expression can appear in braces, not just variables
- Raw strings skip interpolation and escape processing

## Scenarios

### Basic String Interpolation

#### interpolates variable in string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- interpolates variable in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates variable in string")
val name = "Alice"
val result = "Hello, {name}!"
var r = 0
if result == "Hello, Alice!":
    r = 1
expect r == 1
```

</details>

#### interpolates multiple variables

- interpolates multiple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates multiple variables")
val first = "John"
val last = "Doe"
val result = "{first} {last}"
var r = 0
if result == "John Doe":
    r = 1
expect r == 1
```

</details>

#### interpolates at start of string

- interpolates at start of string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates at start of string")
val value = 42
val result = "{value} is the answer"
var r = 0
if result == "42 is the answer":
    r = 1
expect r == 1
```

</details>

#### interpolates at end of string

- interpolates at end of string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates at end of string")
val value = 42
val result = "The answer is {value}"
var r = 0
if result == "The answer is 42":
    r = 1
expect r == 1
```

</details>

### Expression Interpolation

#### interpolates arithmetic expression

- interpolates arithmetic expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates arithmetic expression")
val a = 10
val b = 20
val result = "Sum: {a + b}"
var r = 0
if result == "Sum: 30":
    r = 1
expect r == 1
```

</details>

#### interpolates multiplication expression

- interpolates multiplication expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates multiplication expression")
val x = 5
val y = 3
val result = "Product: {x * y}"
var r = 0
if result == "Product: 15":
    r = 1
expect r == 1
```

</details>

#### interpolates inline conditional expressions without treating colons as formatting

- interpolates inline conditional expressions without treating colons as formatting


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates inline conditional expressions without treating colons as formatting")
val enabled = true
val disabled = false
val result = "values={if enabled: 1 else: 0}/{if disabled: 1 else: 0}"
expect result == "values=1/0"
```

</details>

#### interpolates boolean value

- interpolates boolean value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates boolean value")
val b = true
val result = "flag: {b}"
var r = 0
if result == "flag: true":
    r = 1
expect r == 1
```

</details>

#### interpolates false boolean value

- interpolates false boolean value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates false boolean value")
val b = false
val result = "flag: {b}"
var r = 0
if result == "flag: false":
    r = 1
expect r == 1
```

</details>

### Raw Strings

#### raw string preserves braces

- raw string preserves braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("raw string preserves braces")
val template = r"{name}"
expect template.len() == 6
```

</details>

#### raw string preserves backslashes

- raw string preserves backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("raw string preserves backslashes")
val path = r"C:\Users\test"
expect path.len() == 13
```

</details>

### F-String Syntax

#### f-string basic interpolation

- f-string basic interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("f-string basic interpolation")
val x = 42
val s = f"value is {x}"
var r = 0
if s == "value is 42":
    r = 1
expect r == 1
```

</details>

#### f-string with expression

- f-string with expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("f-string with expression")
val a = 10
val b = 20
val s = f"sum is {a + b}"
var r = 0
if s == "sum is 30":
    r = 1
expect r == 1
```

</details>

#### f-string multiple interpolations

- f-string multiple interpolations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("f-string multiple interpolations")
val name = "world"
val count = 3
val s = f"hello {name}, count={count}"
var r = 0
if s == "hello world, count=3":
    r = 1
expect r == 1
```

</details>

#### f-string no interpolation

- f-string no interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("f-string no interpolation")
val s = f"just a string"
var r = 0
if s == "just a string":
    r = 1
expect r == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `ac648e4bc75f41a3b45da65485f099e40468aa8d73128f2f74b0d674c2ae1a2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac648e4bc75f41a3b45da65485f099e40468aa8d73128f2f74b0d674c2ae1a2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac648e4bc75f41a3b45da65485f099e40468aa8d73128f2f74b0d674c2ae1a2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/string_interpolation_spec.spl
mirror: doc/06_spec/03_system/feature/usage/string_interpolation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/string_interpolation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/string_interpolation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/string_interpolation_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpolates variable in string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/string_interpolation_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpolates multiple variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/string_interpolation_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpolates at start of string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
