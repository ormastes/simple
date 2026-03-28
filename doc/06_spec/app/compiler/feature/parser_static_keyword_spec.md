# Static Keyword Parsing

**Feature ID:** #PARSER-004 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/parser_static_keyword_spec.spl`_

---

## Overview

Tests parsing and resolution of the `static` keyword for class and struct methods.
Covers static method declaration in classes and impl blocks, distinction between
static and instance methods, static factory methods, visibility modifiers
(pub/private), generic static methods, static-to-static calls, default parameters,
complex return types, async static methods, and edge cases.

## Syntax

```simple
class Math:
    static fn add(a: i32, b: i32) -> i32:
        return a + b
expect Math__add(2, 3) == 5
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### Static methods in classes

- ✅ parses static method in class
- ✅ calls static method without instance
- ✅ parses static method with no parameters
- ✅ parses static method returning text
### Static methods in impl blocks

- ✅ parses static method in impl block
- ✅ parses multiple static methods in impl
### Static vs instance methods

- ✅ distinguishes static from instance methods
- ✅ parses class with both static and instance methods
### Static methods as factories

- ✅ uses static method as constructor alternative
- ✅ uses static method with parameters
### Static method visibility

- ✅ parses public static method
- ✅ parses private static method
### Static methods with generics

- ✅ parses static generic method
### Static methods calling other static methods

- ✅ calls static method from another static method
### Static methods with default parameters

- ✅ parses static method with default parameter
### Static methods returning complex types

- ✅ parses static method returning array
- ✅ parses static method returning option
### Static method edge cases

- ✅ parses static method with no return type
- ✅ parses static method with complex expression
- ✅ parses nested static method calls
### Static methods in async contexts

- ✅ parses async static method

