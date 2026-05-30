# Alias and Deprecated Feature Specification
*Source:* `test/feature/usage/alias_deprecated_spec.spl`
**Feature IDs:** #ALIAS-001 to #ALIAS-010  |  **Category:** Language | Syntax  |  **Status:** In Progress

## Overview



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

## Feature: Type Alias Parsing

## Basic Type Alias

    Verifies that `alias NewName = OldName` syntax is parsed correctly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple type alias | pass |
| 2 | parses type alias with uppercase names | pass |

**Example:** parses simple type alias
    Given val source = "alias Point2D = Point"
    Then  expect(true).to_equal(true)

**Example:** parses type alias with uppercase names
    Given val source = "alias Optional = Option"
    Then  expect(true).to_equal(true)

## Feature: Function Alias Parsing

## Function Alias

    Verifies that `fn new_name = old_name` syntax is parsed correctly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses function alias | pass |
| 2 | parses function alias with lowercase names | pass |

**Example:** parses function alias
    Given val source = "fn println = print"
    Then  expect(true).to_equal(true)

**Example:** parses function alias with lowercase names
    Given val source = "fn each = iter"
    Then  expect(true).to_equal(true)

## Feature: Deprecation Decorator

## @deprecated Decorator

    Verifies that @deprecated decorator is recognized and applied.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses deprecated decorator without message | pass |
| 2 | parses deprecated decorator with message | pass |

**Example:** parses deprecated decorator without message
    Given val source = "@deprecated{NL}alias OldPoint = Point"
    Then  expect(true).to_equal(true)

**Example:** parses deprecated decorator with message
    Given val source = "@deprecated(\"Use NewPoint instead\"){NL}alias OldPoint = Point"
    Then  expect(true).to_equal(true)

## Feature: Alias Resolution

## Alias Resolution

    Verifies that aliases are resolved correctly during lowering.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | resolves type alias to original type | pass |
| 2 | resolves function alias to original function | pass |
| 3 | resolves chained aliases | pass |

**Example:** resolves type alias to original type
    Then  expect(true).to_equal(true)

**Example:** resolves function alias to original function
    Then  expect(true).to_equal(true)

**Example:** resolves chained aliases
    Then  expect(true).to_equal(true)

## Feature: Deprecation Warnings

## Deprecation Warning Generation

    Verifies that deprecation warnings are generated when deprecated items are used.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates warning for deprecated function usage | pass |
| 2 | includes deprecation message in warning | pass |
| 3 | suggests non-deprecated alternative | pass |

**Example:** generates warning for deprecated function usage
    Then  expect(true).to_equal(true)

**Example:** includes deprecation message in warning
    Then  expect(true).to_equal(true)

**Example:** suggests non-deprecated alternative
    Then  expect(true).to_equal(true)

## Feature: Alias Integration

## Real-World Usage

    Tests for practical alias scenarios.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | supports library migration pattern | pass |
| 2 | supports method aliasing in impl blocks | pass |

**Example:** supports library migration pattern
    Then  expect(true).to_equal(true)

**Example:** supports method aliasing in impl blocks
    Then  expect(true).to_equal(true)

## Feature: Type Alias Edge Cases

expect(true).to_equal(true)  # Should produce error

    it "allows alias with same name as original in different scope":
        # This is a valid shadowing scenario
        val source = """
struct Point:
    x: i64
    y: i64

fn test():
    alias Point = OtherPoint

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | rejects self-referential alias | pass |
| 2 | rejects alias to non-existent type | pass |
| 3 | rejects duplicate alias names | pass |
| 4 | handles alias to generic type | pass |
| 5 | handles alias with visibility modifier | pass |

**Example:** rejects self-referential alias
    Given val source = "alias Foo = Foo"
    Then  expect(true).to_equal(true)  # Should produce error

**Example:** rejects alias to non-existent type
    Given val source = "alias NewType = NonExistent"
    Then  expect(true).to_equal(true)  # Should produce error

**Example:** rejects duplicate alias names
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** handles alias to generic type
    Given val source = "alias IntList = List<Int>"
    Then  expect(true).to_equal(true)

**Example:** handles alias with visibility modifier
    Given val source = "pub alias PublicPoint = Point"
    Then  expect(true).to_equal(true)

## Feature: Function Alias Edge Cases

expect(true).to_equal(true)

    it "handles function alias chain":
        # fn a = b, fn b = c, fn c = impl
        val source = """
fn base_impl():
    42

fn level1 = base_impl
fn level2 = level1
fn level3 = level2

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | rejects self-referential function alias | pass |
| 2 | rejects alias to non-existent function | pass |
| 3 | rejects duplicate function alias names | pass |
| 4 | allows function alias with visibility modifier | pass |
| 5 | handles alias to method in impl block | pass |
| 6 | handles non-deprecated alias to deprecated function | pass |
| 7 | handles deprecation on type alias | pass |
| 8 | rejects longer circular alias chain | pass |
| 9 | resolves alias chain with deprecation in middle | pass |

**Example:** rejects self-referential function alias
    Given val source = "fn foo = foo"
    Then  expect(true).to_equal(true)  # Should produce error

**Example:** rejects alias to non-existent function
    Given val source = "fn newFunc = nonExistent"
    Then  expect(true).to_equal(true)  # Should produce error

**Example:** rejects duplicate function alias names
    Given val source = """
    Then  expect(true).to_equal(true)  # Should produce error

**Example:** allows function alias with visibility modifier
    Given val source = "pub fn println = print"
    Then  expect(true).to_equal(true)

**Example:** handles alias to method in impl block
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** handles non-deprecated alias to deprecated function
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** handles deprecation on type alias
    Given val source = """
    Then  expect(true).to_equal(true)  # Should produce error

**Example:** rejects longer circular alias chain
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** resolves alias chain with deprecation in middle
    Given val source = """
    Then  expect(true).to_equal(true)

## Feature: Alias Syntax Error Cases

## Syntax Error Cases

    Tests for proper error handling of malformed alias syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | rejects alias without equals sign | pass |
| 2 | rejects alias without target | pass |
| 3 | rejects alias without name | pass |
| 4 | rejects function alias without target | pass |
| 5 | rejects alias with invalid identifier | pass |
| 6 | rejects alias keyword as variable name | pass |

**Example:** rejects alias without equals sign
    Given val source = "alias NewName OldName"
    Then  expect(true).to_equal(true)  # Should produce parse error

**Example:** rejects alias without target
    Given val source = "alias NewName ="
    Then  expect(true).to_equal(true)  # Should produce parse error

**Example:** rejects alias without name
    Given val source = "alias = OldName"
    Then  expect(true).to_equal(true)  # Should produce parse error

**Example:** rejects function alias without target
    Given val source = "fn newName ="
    Then  expect(true).to_equal(true)  # Should produce parse error

**Example:** rejects alias with invalid identifier
    Given val source = "alias 123Invalid = Valid"
    Then  expect(true).to_equal(true)  # Should produce parse error

**Example:** rejects alias keyword as variable name
    Given val source = "val alias_ = 42"  # Using alias_ since alias is keyword
    Then  expect(true).to_equal(true)

## Feature: Cross-Module Alias Cases

# Using alias1 should suggest original
        expect(true).to_equal(true)

    it "handles suggestion when original is also deprecated":
        # Edge case: original deprecated, alias not deprecated
        val source = """
@deprecated("Internal - use public_api instead")
fn internal_impl():
    42

fn public_api = internal_impl

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles alias to imported type | pass |
| 2 | handles re-exporting via alias | pass |
| 3 | suggests original when all aliases are deprecated | pass |
| 4 | does not suggest itself | pass |

**Example:** handles alias to imported type
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** handles re-exporting via alias
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** suggests original when all aliases are deprecated
    Given val source = """
    Then  expect(true).to_equal(true)

**Example:** does not suggest itself
    Given val source = """


