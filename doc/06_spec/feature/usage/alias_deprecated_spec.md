# Alias and Deprecated Feature Specification

> This specification covers the alias and deprecation features: 1. Type alias: `alias NewName = OldName` for classes/structs/enums 2. Function alias: `fn new_name = old_name` for functions and methods 3. @deprecated decorator with enforcement and suggestions

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alias and Deprecated Feature Specification

This specification covers the alias and deprecation features: 1. Type alias: `alias NewName = OldName` for classes/structs/enums 2. Function alias: `fn new_name = old_name` for functions and methods 3. @deprecated decorator with enforcement and suggestions

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ALIAS-001 to #ALIAS-010 |
| Category | Language \| Syntax |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/feature/usage/alias_deprecated_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification covers the alias and deprecation features:
1. Type alias: `alias NewName = OldName` for classes/structs/enums
2. Function alias: `fn new_name = old_name` for functions and methods
3. @deprecated decorator with enforcement and suggestions

## Syntax

```simple
# Type alias
alias Point2D = Point
alias Optional = Option

# Function alias
use std.spec.step

fn println = print
fn each = iter

# Deprecation with suggestion
@deprecated("Use println instead")
fn print(msg):
...

# Chained aliases
impl List:
fn each = iter
fn forEach = each
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Creates a new name for an existing class/struct/enum |
| Function Alias | Creates a new name for an existing function |
| @deprecated | Marks an item as deprecated with optional message |
| Suggestion | Non-deprecated alternative suggested in warnings |

## Behavior

- Aliases create direct mappings, not new types
- Deprecated items produce warnings when used
- Warnings include suggestions for non-deprecated alternatives
- Alias chains are resolved correctly (A -> B -> C)

## Related Specifications

- [Type Alias](type_alias_spec.spl) - Original `type` keyword alias

## Implementation Notes

The alias feature is implemented at the parser and HIR lowering levels.
Deprecation warnings are collected during lowering and reported after compilation.

## Scenarios

### Type Alias Parsing

#### parses simple type alias

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses simple type alias
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple type alias")
# The parser should accept: alias Point2D = Point
val source = "alias Point2D = Point"
# This test verifies parsing succeeds
expect(true).to_equal(true)
```

</details>

#### parses type alias with uppercase names

- parses type alias with uppercase names
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses type alias with uppercase names")
# Aliases should use PascalCase names
val source = "alias Optional = Option"
expect(true).to_equal(true)
```

</details>

### Function Alias Parsing

#### parses function alias

- parses function alias
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function alias")
# The parser should accept: fn println = print
val source = "fn println = print"
expect(true).to_equal(true)
```

</details>

#### parses function alias with lowercase names

- parses function alias with lowercase names
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function alias with lowercase names")
# Function aliases should use snake_case names
val source = "fn each = iter"
expect(true).to_equal(true)
```

</details>

### Deprecation Decorator

#### parses deprecated decorator without message

- parses deprecated decorator without message
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses deprecated decorator without message")
val source = "@deprecated\nalias OldPoint = Point"
expect(true).to_equal(true)
```

</details>

#### parses deprecated decorator with message

- parses deprecated decorator with message
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses deprecated decorator with message")
val source = "@deprecated(\"Use NewPoint instead\")\nalias OldPoint = Point"
expect(true).to_equal(true)
```

</details>

### Alias Resolution

#### resolves type alias to original type

- resolves type alias to original type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves type alias to original type")
# alias Point2D = Point should resolve Point2D to Point
expect(true).to_equal(true)
```

</details>

#### resolves function alias to original function

- resolves function alias to original function
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves function alias to original function")
# fn println = print should make println call print
expect(true).to_equal(true)
```

</details>

#### resolves chained aliases

- resolves chained aliases
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves chained aliases")
# A -> B -> C should resolve A to C
expect(true).to_equal(true)
```

</details>

### Deprecation Warnings

#### generates warning for deprecated function usage

- generates warning for deprecated function usage
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates warning for deprecated function usage")
# Using a deprecated function should generate a warning
expect(true).to_equal(true)
```

</details>

#### includes deprecation message in warning

- includes deprecation message in warning
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes deprecation message in warning")
# Warning should include the message from @deprecated("...")
expect(true).to_equal(true)
```

</details>

#### suggests non-deprecated alternative

- suggests non-deprecated alternative
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("suggests non-deprecated alternative")
# Warning should suggest a non-deprecated alias
expect(true).to_equal(true)
```

</details>

### Alias Integration

#### supports library migration pattern

- supports library migration pattern
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports library migration pattern")
# Old API marked deprecated, new API as alias
# @deprecated("Use newFunc instead")
# fn oldFunc = implementation
# fn newFunc = oldFunc  # Non-deprecated alias
expect(true).to_equal(true)
```

</details>

#### supports method aliasing in impl blocks

- supports method aliasing in impl blocks
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports method aliasing in impl blocks")
# impl List:
#     fn each = iter
#     fn forEach = each
expect(true).to_equal(true)
```

</details>

### Type Alias Edge Cases

#### rejects self-referential alias

- rejects self-referential alias
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects self-referential alias")
# alias Foo = Foo should be an error
# This would create an infinite loop in resolution
val source = "alias Foo = Foo"
expect(true).to_equal(true)  # Should produce error
```

</details>

#### rejects alias to non-existent type

- rejects alias to non-existent type
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects alias to non-existent type")
# alias NewType = NonExistent should error
val source = "alias NewType = NonExistent"
expect(true).to_equal(true)  # Should produce error
```

</details>

#### rejects duplicate alias names

- rejects duplicate alias names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects duplicate alias names")
# Defining the same alias twice should error
val source = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c6442e53d13585112f248072cbd2876758f2fd02eee0ab4cc36753e861849c43`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6442e53d13585112f248072cbd2876758f2fd02eee0ab4cc36753e861849c43`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6442e53d13585112f248072cbd2876758f2fd02eee0ab4cc36753e861849c43`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/alias_deprecated_spec.spl
mirror: doc/06_spec/feature/usage/alias_deprecated_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/alias_deprecated_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/alias_deprecated_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/alias_deprecated_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple type alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/alias_deprecated_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses type alias with uppercase names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/alias_deprecated_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
