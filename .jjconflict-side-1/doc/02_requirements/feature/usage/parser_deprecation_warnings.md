# Parser Deprecation Warnings Specification
*Source:* `test/feature/usage/parser_deprecation_warnings_spec.spl`
**Feature IDs:** #PARSER-DEPREC-001 to #PARSER-DEPREC-031  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview



Tests that the parser correctly emits deprecation warnings for
deprecated syntax (e.g., [] for generics instead of <>).

## Key Deprecations

- Generic syntax: `[]` deprecated in favor of `<>`
- Affects: functions, structs, classes, enums, traits, impl blocks
- Array types `[i32]` and literals `[1,2,3]` should NOT warn

## API

```simple
use std.parser.{Parser, ErrorHint, ErrorHintLevel}

var parser = Parser.new(source)
parser.parse()
val hints = parser.error_hints()
```

## Feature: Function Generic Deprecation Warnings

## Generic Function Syntax

    Tests deprecation warnings for function generic parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | warns about deprecated [] syntax in function generics | pass |
| 2 | warns about deprecated [] syntax with multiple params | pass |
| 3 | does NOT warn about <> syntax in function generics | pass |

**Example:** warns about deprecated [] syntax in function generics
    Given var parser = Parser.new("fn test[T](x: T) -> T:{NL}    x")
    Given val hints = parser.error_hints()
    Given val has_warning = hints.any(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated"))
    Then  expect has_warning

**Example:** warns about deprecated [] syntax with multiple params
    Given var parser = Parser.new("fn map[T, U](f: fn(T) -> U) -> U:{NL}    pass")
    Given val hints = parser.error_hints()
    Given val has_warning = hints.any(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated"))
    Then  expect has_warning

**Example:** does NOT warn about <> syntax in function generics
    Given var parser = Parser.new("fn test<T>(x: T) -> T:{NL}    x")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: Struct Generic Deprecation Warnings

## Generic Struct Syntax

    Tests deprecation warnings for struct generic parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | warns about deprecated [] syntax in struct | pass |
| 2 | does NOT warn about <> syntax in struct | pass |

**Example:** warns about deprecated [] syntax in struct
    Given var parser = Parser.new("struct Container[T]:{NL}    value: T")
    Given val hints = parser.error_hints()
    Given val has_warning = hints.any(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated"))
    Then  expect has_warning

**Example:** does NOT warn about <> syntax in struct
    Given var parser = Parser.new("struct Container<T>:{NL}    value: T")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: Type Annotation Deprecation Warnings

## Generic Type Annotation Syntax

    Tests deprecation warnings for type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | warns about deprecated [] syntax in Option type | pass |
| 2 | warns about deprecated [] syntax in Result type | pass |
| 3 | warns about deprecated [] syntax in List type | pass |
| 4 | does NOT warn about <> syntax in type annotation | pass |

**Example:** warns about deprecated [] syntax in Option type
    Given var parser = Parser.new("val x: Option[Int] = None")
    Given val hints = parser.error_hints()
    Given val has_warning = hints.any(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated"))
    Then  expect has_warning

**Example:** warns about deprecated [] syntax in Result type
    Given var parser = Parser.new("val x: Result[Int, String] = Ok(42)")
    Given val hints = parser.error_hints()
    Given val has_warning = hints.any(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated"))
    Then  expect has_warning

**Example:** warns about deprecated [] syntax in List type
    Given var parser = Parser.new("val nums: List[Int] = []")
    Given val hints = parser.error_hints()
    Given val has_warning = hints.any(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated"))
    Then  expect has_warning

**Example:** does NOT warn about <> syntax in type annotation
    Given var parser = Parser.new("val x: Option<Int> = None")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: Nested Generic Deprecation Warnings

## Nested Generic Syntax

    Tests deprecation warnings for nested generic types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | warns about both nested [] usages | pass |
| 2 | does NOT warn about nested <> syntax | pass |

**Example:** warns about both nested [] usages
    Given var parser = Parser.new("val x: List[Option[String]] = []")
    Given val hints = parser.error_hints()
    Given val warning_count = hints.filter(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated")).len()
    Then  expect warning_count >= 2

**Example:** does NOT warn about nested <> syntax
    Given var parser = Parser.new("val x: List<Option<String>> = []")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: Array Type No Deprecation Warnings

## Array Type Syntax

    Tests that array types do NOT trigger deprecation warnings.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | does NOT warn about array type [i32] | pass |
| 2 | does NOT warn about fixed-size array [i32; 10] | pass |

**Example:** does NOT warn about array type [i32]
    Given var parser = Parser.new("val arr: [i32] = [1, 2, 3]")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

**Example:** does NOT warn about fixed-size array [i32; 10]
    Given var parser = Parser.new("val arr: [i32; 10] = []")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: Array Literal No Deprecation Warnings

## Array Literal Syntax

    Tests that array literals do NOT trigger deprecation warnings.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | does NOT warn about array literal | pass |
| 2 | does NOT warn about empty array literal | pass |

**Example:** does NOT warn about array literal
    Given var parser = Parser.new("val arr = [1, 2, 3, 4, 5]")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

**Example:** does NOT warn about empty array literal
    Given var parser = Parser.new("val arr = []")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: String and Comment No Deprecation Warnings

## Bracket Syntax in Strings/Comments

    Tests that [] in strings and comments do NOT trigger warnings.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | does NOT warn about [] in string literal | pass |
| 2 | does NOT warn about [] in comment | pass |

**Example:** does NOT warn about [] in string literal
    Given var parser = Parser.new(r'val s = "This is List[T] in a string"')
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

**Example:** does NOT warn about [] in comment
    Given var parser = Parser.new("# This is Option[T] in a comment{NL}val x = 42")
    Given val hints = parser.error_hints()
    Given val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
    Then  expect not has_deprecation

## Feature: Multiple Deprecation Warnings

it "warns about [] in impl block":
        var parser = Parser.new("impl[T] Container[T]:{NL}    fn new(val: T) -> Container[T]:{NL}        pass")
        parser.parse()
        val hints = parser.error_hints()
        val warning_count = hints.filter(\h: h.level == ErrorHintLevel.Warning and h.message.contains("Deprecated")).len()
        expect warning_count >= 2

    it "does NOT warn about <> in impl block":
        var parser = Parser.new("impl<T> Container<T>:{NL}    fn new(val: T) -> Container<T>:{NL}        pass")
        parser.parse()
        val hints = parser.error_hints()
        val has_deprecation = hints.any(\h: h.message.contains("Deprecated") and h.message.contains("generic"))
        expect not has_deprecation


# ============================================================================
# Test Group 15: Edge Cases
# ============================================================================

describe "Deprecation Warning Edge Cases":

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | warns about multiple deprecations in same file | pass |

**Example:** warns about multiple deprecations in same file
    Given val source = """
    Given val opt: Option[String] = None


