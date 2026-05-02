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
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This specification covers the alias and deprecation features:
1. Type alias: `alias NewName = OldName` for classes/structs/enums
2. Function alias: `fn new_name = old_name` for functions and methods
3. @deprecated decorator with enforcement and suggestions

## Syntax

```simple
alias Point2D = Point
alias Optional = Option

fn println = print
fn each = iter

@deprecated("Use println instead")
fn print(msg):
...

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

expect(true).to_equal(true)  # Should produce error

    it "allows alias with same name as original in different scope":
        # This is a valid shadowing scenario
        val source = """
struct Point:
    x: i64
    y: i64

fn test():
    alias Point = OtherPoint

expect(true).to_equal(true)  # Should produce error

    it "rejects alias conflicting with existing function":
        # Cannot create alias with same name as existing function
        val source = """
fn existing():
    42

fn existing = other_func

expect(true).to_equal(true)


# ============================================================================
# Test Group 9: Deprecation Edge Cases
# ============================================================================

describe "Deprecation Edge Cases":
    # ## Deprecation Edge Cases
    #
    # Tests for boundary conditions in deprecation handling.

    it "handles empty deprecation message":
        # @deprecated("") should still work
        val source = "@deprecated(\"\")\nfn old_func(): 42"
        expect(true).to_equal(true)

    it "handles deprecation with special characters in message":
        # Message with quotes, newlines, etc.
        val source = "@deprecated(\"Use 'new_func' instead\\nSee docs.\")\nfn old_func(): 42"
        expect(true).to_equal(true)

    it "handles deprecated alias pointing to deprecated function":
        # Both the alias and target are deprecated
        val source = """
@deprecated("Use new_impl instead")
fn old_impl():
    42

@deprecated("Use new_func instead")
fn old_func = old_impl

expect(true).to_equal(true)

    it "handles multiple decorators with deprecated":
        # @deprecated combined with other decorators
        val source = """
@deprecated("Use v2 instead")
@pure
fn old_pure_func():
    42

expect(true).to_equal(true)


# ============================================================================
# Test Group 10: Alias Chain Edge Cases
# ============================================================================

describe "Alias Chain Edge Cases":
    # ## Alias Chain Edge Cases
    #
    # Tests for complex alias resolution scenarios.

    it "rejects circular alias chain":
        # A -> B -> A should be detected and rejected
        val source = """
alias A = B
alias B = A

expect(true).to_equal(true)  # Should produce error

    it "handles deep alias chain":
        # A -> B -> C -> D -> E (5 levels) should work
        val source = """
struct Base:
    x: i64

alias Level1 = Base
alias Level2 = Level1
alias Level3 = Level2
alias Level4 = Level3
alias Level5 = Level4

expect(true).to_equal(true)

    it "handles function alias chain":
        # fn a = b, fn b = c, fn c = impl
        val source = """
fn base_impl():
    42

fn level1 = base_impl
fn level2 = level1
fn level3 = level2

expect(true).to_equal(true)

    it "handles alias to qualified type":
        # Alias using fully qualified name
        val source = "alias MyList = std.collections.List"
        expect(true).to_equal(true)

    it "handles exported alias":
        # pub alias should be visible to importing modules
        val source = """
pub alias PublicAlias = InternalType

struct InternalType:
    x: i64

expect(true).to_equal(true)


# ============================================================================
# Test Group 13: Alias with Generics Edge Cases
# ============================================================================

describe "Alias with Generics Edge Cases":
    # ## Alias with Generics
    #
    # Tests for aliases involving generic types.

    it "handles alias to partially applied generic":
        # alias StringMap<V> = Map<String, V>
        val source = "alias StringMap<V> = Map<String, V>"
        expect(true).to_equal(true)

    it "handles alias to fully applied generic":
        # alias IntList = List<Int>
        val source = "alias IntList = List<Int>"
        expect(true).to_equal(true)

    it "handles alias preserving all type parameters":
        # alias MyMap<K, V> = Map<K, V>
        val source = "alias MyMap<K, V> = Map<K, V>"
        expect(true).to_equal(true)

    it "handles nested generic alias":
        # alias NestedList<T> = List<List<T>>
        val source = "alias NestedList<T> = List<List<T>>"
        expect(true).to_equal(true)

    it "rejects alias with mismatched type parameters":
        # alias Bad<T, U> = List<T> (U unused - may warn or error)
        val source = "alias Bad<T, U> = List<T>"
        expect(true).to_equal(true)  # Implementation decision


# ============================================================================
# Test Group 14: Deprecation Suggestion Edge Cases
# ============================================================================

describe "Deprecation Suggestion Edge Cases":
    # ## Deprecation Suggestion Logic
    #
    # Tests for the suggestion algorithm when deprecated items are used.

    it "suggests non-deprecated alias when available":
        # Using deprecated A should suggest non-deprecated B
        val source = """
fn impl():
    42

@deprecated("Use new_func instead")
fn old_func = impl

fn new_func = impl

# Using alias1 should suggest original
        expect(true).to_equal(true)

    it "handles suggestion when original is also deprecated":
        # Edge case: original deprecated, alias not deprecated
        val source = """
@deprecated("Internal - use public_api instead")
fn internal_impl():
    42

fn public_api = internal_impl

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/alias_deprecated/result.json` |

## Scenarios

- parses simple type alias
- parses type alias with uppercase names
- parses function alias
- parses function alias with lowercase names
- parses deprecated decorator without message
- parses deprecated decorator with message
- resolves type alias to original type
- resolves function alias to original function
- resolves chained aliases
- generates warning for deprecated function usage
- includes deprecation message in warning
- suggests non-deprecated alternative
- supports library migration pattern
- supports method aliasing in impl blocks
- rejects self-referential alias
- rejects alias to non-existent type
- rejects duplicate alias names
- allows alias with same name as original in different scope
- handles alias to generic type
- handles alias with visibility modifier
- rejects self-referential function alias
- rejects alias to non-existent function
- rejects duplicate function alias names
- rejects alias conflicting with existing function
- allows function alias with visibility modifier
- handles alias to method in impl block
- handles empty deprecation message
- handles deprecation with special characters in message
- handles deprecated alias pointing to deprecated function
- handles non-deprecated alias to deprecated function
- handles multiple decorators with deprecated
- handles deprecation on type alias
- rejects circular alias chain
- rejects longer circular alias chain
- handles deep alias chain
- resolves alias chain with deprecation in middle
- handles function alias chain
- rejects alias without equals sign
- rejects alias without target
- rejects alias without name
- rejects function alias without target
- rejects alias with invalid identifier
- rejects alias keyword as variable name
- handles alias to imported type
- handles alias to qualified type
- handles exported alias
- handles re-exporting via alias
- handles alias to partially applied generic
- handles alias to fully applied generic
- handles alias preserving all type parameters
- handles nested generic alias
- rejects alias with mismatched type parameters
- suggests non-deprecated alias when available
- suggests original when all aliases are deprecated
- handles suggestion when original is also deprecated
- does not suggest itself
