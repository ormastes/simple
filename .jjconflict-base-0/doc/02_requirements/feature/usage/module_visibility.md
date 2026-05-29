# Module Visibility Specification
*Source:* `test/feature/usage/module_visibility_spec.spl`
**Feature IDs:** #LANG-042 (Feature DB ID: 300)  |  **Category:** Language  |  **Status:** In Progress (Core Complete, Integration Pending)

## Overview



## Overview

Module visibility system with filename-based auto-public rule. Types matching
the filename are automatically public; all other declarations are private by
default unless explicitly marked with `public`.

This enables top-level `val` declarations (private by default) and provides
clear visibility control for APIs.

## Syntax

```simple
# file: test_case.spl

# Auto-public: name matches filename (snake_case -> PascalCase)
class TestCase:
    id: i32

# Private by default (name doesn't match)
class Helper:
    data: i32

# Explicit public
public class PublicHelper:
    data: i32

# Top-level val (private by default)
val CONSTANT: i32 = 42

# Explicit public constant
public val PUBLIC_CONSTANT: i32 = 100

# Private function (default)
fn helper_fn(): pass

# Public function (explicit)
public fn public_fn(): pass
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Filename Match | Type name matching filename is auto-public |
| Private Default | All other declarations are private by default |
| `public` Keyword | Explicitly marks declaration as public |
| `private` Keyword | Explicitly marks declaration as private (optional) |
| Top-level `val` | Module-level constants, private by default |
| Name Conversion | snake_case filename -> PascalCase type |

## Behavior

- `test_case.spl` -> `class TestCase` is auto-public
- Other classes/structs in file are private by default
- Functions are private by default
- Top-level `val`/`var` are private by default
- Use `public` keyword to export additional items
- `mod.spl` files are for re-exports only (no auto-public type)

## Related Specifications

- Module System - Import/export mechanics
- Type System - Type visibility in type checking
- Code Quality Tools - Visibility linting

## Feature: Module Visibility Filename Match

## Filename-Based Auto-Public Rule

    Verifies that types matching the filename (after snake_case to PascalCase
    conversion) are automatically public.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | auto-publics class matching filename | pass |
| 2 | converts snake_case filename to PascalCase | pass |
| 3 | makes non-matching types private by default | pass |

**Example:** auto-publics class matching filename
    Given val is_public = effective_visibility("TestCase", "test_case.spl", false)
    Then  expect is_public

**Example:** converts snake_case filename to PascalCase
    Then  expect filename_to_type_name("string_interner.spl") == "StringInterner"
    Then  expect filename_to_type_name("http_client.spl") == "HttpClient"
    Then  expect filename_to_type_name("io.spl") == "Io"

**Example:** makes non-matching types private by default
    Given val is_public = effective_visibility("Helper", "test_case.spl", false)
    Then  expect not is_public

## Feature: Module Visibility Keywords

## Public/Private Keywords

    Tests explicit visibility modifiers for declarations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | supports public keyword for classes | pass |
| 2 | supports public keyword for functions | pass |
| 3 | supports private keyword (explicit) | pass |
| 4 | allows redundant private on non-matching types | pass |

**Example:** supports public keyword for classes
    Given val is_public = effective_visibility("ExplicitPublic", "test_case.spl", true)
    Then  expect is_public

**Example:** supports public keyword for functions
    Given val is_public = effective_visibility("exported_function", "test_case.spl", true)
    Then  expect is_public

**Example:** supports private keyword (explicit)
    Given val is_public = effective_visibility("ExplicitPrivate", "test_case.spl", false)
    Then  expect not is_public

**Example:** allows redundant private on non-matching types
    Given val is_public = effective_visibility("Helper", "test_case.spl", false)
    Then  expect not is_public

## Feature: Module Visibility Top-Level Val

## Top-Level Constants

    With visibility system, top-level `val` becomes possible.
    Private by default, can be made public explicitly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows private top-level val | pass |
| 2 | allows public top-level val | pass |
| 3 | allows top-level val in expressions | pass |
| 4 | rejects mutable top-level var without explicit public | pass |

**Example:** allows private top-level val
    Given val is_public = effective_visibility("PRIVATE_CONST", "test_case.spl", false)
    Then  expect not is_public

**Example:** allows public top-level val
    Given val is_public = effective_visibility("PUBLIC_CONST", "test_case.spl", true)
    Then  expect is_public

**Example:** allows top-level val in expressions
    Given val a_public = effective_visibility("A", "test_case.spl", false)
    Given val b_public = effective_visibility("B", "test_case.spl", false)
    Then  expect not a_public
    Then  expect not b_public

**Example:** rejects mutable top-level var without explicit public
    Given val is_public = effective_visibility("counter", "test_case.spl", false)
    Then  expect not is_public

## Feature: Module Visibility Impl Blocks

## Impl Block Method Visibility

    Methods inherit visibility context from their target type.
    Uses VisibilityChecker to verify cross-module access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | methods on public type are public by default | pass |
| 2 | methods on private type are private | pass |
| 3 | allows private methods on public type | pass |

**Example:** methods on public type are public by default
    Given val checker = VisibilityChecker.new("other.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect not warning.?

**Example:** methods on private type are private
    Given val checker = VisibilityChecker.new("other.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect warning.?

**Example:** allows private methods on public type
    Given val sym = Symbol(
    Given val cross_checker = VisibilityChecker.new("other.spl")
    Given val cross_warning = cross_checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect cross_warning.?
    Given val same_checker = VisibilityChecker.new("test_case.spl")
    Given val same_warning = same_checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect not same_warning.?

## Feature: Module Visibility Diagnostics

## Warning and Error Messages

    Tests compiler diagnostics for visibility issues.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | warns on implicitly public non-matching type (phase 1) | pass |
| 2 | warns on implicitly public function (phase 1) | pass |
| 3 | errors on accessing private type (phase 2) | pass |
| 4 | suggests adding public modifier in warning | pass |

**Example:** warns on implicitly public non-matching type (phase 1)
    Given val checker = VisibilityChecker.new("other.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect warning.?
    Then  expect warning.unwrap().code == "W0401"

**Example:** warns on implicitly public function (phase 1)
    Given val checker = VisibilityChecker.new("other.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect warning.?
    Then  expect warning.unwrap().code == "W0401"

**Example:** errors on accessing private type (phase 2)
    Given val checker = VisibilityChecker.new("other.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "test_case.spl", Span.empty())
    Then  expect warning.?

**Example:** suggests adding public modifier in warning
    Given val w = VisibilityWarning.new("Helper", "other.spl", "test_case.spl", Span.empty())
    Given val formatted = w.format()
    Then  expect formatted.contains("pub")

## Feature: Module Visibility Re-exports

## Module Re-exports

    Special handling for mod.spl files which are for re-exporting only.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | mod.spl has no auto-public type | pass |

**Example:** mod.spl has no auto-public type
    Then  expect not type_matches_filename("Mod", "mod.spl")
    Then  expect not effective_visibility("Mod", "mod.spl", false)

## Feature: Module Visibility Import Integration

## Import System Integration

    Tests that visibility correctly interacts with the import system.
    Uses VisibilityChecker to verify cross-module access patterns.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows importing public items | pass |
| 2 | rejects importing private items | pass |
| 3 | allows qualified access to public items | pass |

**Example:** allows importing public items
    Given val checker = VisibilityChecker.new("consumer.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "provider.spl", Span.empty())
    Then  expect not warning.?

**Example:** rejects importing private items
    Given val checker = VisibilityChecker.new("consumer.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "provider.spl", Span.empty())
    Then  expect warning.?
    Then  expect warning.unwrap().code == "W0401"

**Example:** allows qualified access to public items
    Given val checker = VisibilityChecker.new("consumer.spl")
    Given val sym = Symbol(
    Given val warning = checker.check_symbol_access(sym, "provider.spl", Span.empty())
    Then  expect not warning.?

## Feature: Module Visibility Edge Cases

## Edge Cases and Special Scenarios

    Tests unusual but valid visibility scenarios.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles multiple types with same prefix | pass |
| 2 | handles single-word filenames | pass |
| 3 | handles acronyms in filenames | pass |
| 4 | handles nested types visibility | pass |

**Example:** handles multiple types with same prefix
    Then  expect type_matches_filename("TestCase", "test_case.spl")
    Then  expect not type_matches_filename("TestCaseBuilder", "test_case.spl")

**Example:** handles single-word filenames
    Then  expect type_matches_filename("Io", "io.spl")

**Example:** handles acronyms in filenames
    Then  expect filename_to_type_name("http_api.spl") == "HttpApi"

**Example:** handles nested types visibility
    Given val parent_sym = Symbol(
    Given val inner_sym = Symbol(
    Given val checker = VisibilityChecker.new("other.spl")
    Given val parent_warning = checker.check_symbol_access(parent_sym, "outer.spl", Span.empty())
    Given val inner_warning = checker.check_symbol_access(inner_sym, "outer.spl", Span.empty())
    Then  expect not parent_warning.?
    Then  expect not inner_warning.?


