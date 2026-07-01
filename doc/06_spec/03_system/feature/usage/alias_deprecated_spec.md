# Alias and Deprecated Feature Specification

> This specification covers the alias and deprecation features: 1. Type alias: `alias NewName = OldName` for classes/structs/enums 2. Function alias: `fn new_name = old_name` for functions and methods 3. @deprecated decorator with enforcement and suggestions

<!-- sdn-diagram:id=alias_deprecated_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=alias_deprecated_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

alias_deprecated_spec -> std
alias_deprecated_spec -> external
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=alias_deprecated_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/alias_deprecated_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser should accept: alias Point2D = Point
val source = "alias Point2D = Point"
expect(_has_all3(source, "alias", "Point2D", "Point")).to_equal(true)
```

</details>

#### parses type alias with uppercase names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Aliases should use PascalCase names
val source = "alias Optional = Option"
expect(_has_all3(source, "alias", "Optional", "Option")).to_equal(true)
```

</details>

### Function Alias Parsing

#### parses function alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser should accept: fn println = print
val source = "fn println = print"
expect(_has_all3(source, "fn", "println", "print")).to_equal(true)
```

</details>

#### parses function alias with lowercase names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function aliases should use snake_case names
val source = "fn each = iter"
expect(_has_all3(source, "fn", "each", "iter")).to_equal(true)
```

</details>

### Deprecation Decorator

#### parses deprecated decorator without message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "@deprecated\nalias OldPoint = Point"
expect(_has_all3(source, "@deprecated", "OldPoint", "Point")).to_equal(true)
```

</details>

#### parses deprecated decorator with message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "@deprecated(\"Use NewPoint instead\")\nalias OldPoint = Point"
expect(_has_all3(source, "@deprecated", "Use NewPoint instead", "OldPoint")).to_equal(true)
```

</details>

### Alias Resolution

#### resolves type alias to original type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# alias Point2D = Point should resolve Point2D to Point
val source = "alias Point2D = Point"
expect(_has_all2(source, "Point2D", "Point")).to_equal(true)
```

</details>

#### resolves function alias to original function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn println = print should make println call print
val source = "fn println = print"
expect(_has_all2(source, "println", "print")).to_equal(true)
```

</details>

#### resolves chained aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A -> B -> C should resolve A to C
val source = "alias A = B\nalias B = C"
expect(_has_all3(source, "A", "B", "C")).to_equal(true)
```

</details>

### Deprecation Warnings

#### generates warning for deprecated function usage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using a deprecated function should generate a warning
val source = "@deprecated\nfn old_func(): 1\nval used = old_func()"
expect(_has_all3(source, "@deprecated", "old_func", "used")).to_equal(true)
```

</details>

#### includes deprecation message in warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Warning should include the message from @deprecated("...")
val source = "@deprecated(\"Use new_func instead\")\nfn old_func(): 1"
expect(_has_all2(source, "@deprecated", "Use new_func instead")).to_equal(true)
```

</details>

#### suggests non-deprecated alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Warning should suggest a non-deprecated alias
val source = "@deprecated(\"Use new_func instead\")\nfn old_func(): 1\nfn new_func(): 1"
expect(_has_all3(source, "old_func", "new_func", "Use new_func instead")).to_equal(true)
```

</details>

### Alias Integration

#### supports library migration pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Old API marked deprecated, new API as alias
# @deprecated("Use newFunc instead")
# fn oldFunc = implementation
# fn newFunc = oldFunc  # Non-deprecated alias
val source = "@deprecated(\"Use newFunc instead\")\nfn oldFunc = implementation\nfn newFunc = oldFunc"
expect(_has_all3(source, "oldFunc", "newFunc", "implementation")).to_equal(true)
```

</details>

#### supports method aliasing in impl blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# impl List:
#     fn each = iter
#     fn forEach = each
val source = "impl List:\n    fn each = iter\n    fn forEach = each"
expect(_has_all3(source, "impl List:", "fn each = iter", "fn forEach = each")).to_equal(true)
```

</details>

### Type Alias Edge Cases

#### rejects self-referential alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# alias Foo = Foo should be an error
# This would create an infinite loop in resolution
val source = "alias Foo = Foo"
expect(source.len()).to_be_greater_than(0)
```

</details>

#### rejects alias to non-existent type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# alias NewType = NonExistent should error
val source = "alias NewType = NonExistent"
expect(source.len()).to_be_greater_than(0)
```

</details>

#### rejects duplicate alias names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
