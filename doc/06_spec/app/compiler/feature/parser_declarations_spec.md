# Parser Declaration Specification

**Feature ID:** #PARSER-DECL-001 to #PARSER-DECL-025 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_declarations_spec.spl`_

---

## Syntax

```simple
struct Point:
    x: i64
    y: i64

enum Color:
    Red
    Green
    Blue

class Service:
    field: Type

trait Printable:
    fn print()

module utils:
    fn helper():
        pass

import module.submodule
type Alias = OriginalType
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 38 |

## Test Structure

### Struct Declaration Parsing

#### basic structs

- ✅ parses struct with fields
- ✅ parses struct with single field
- ✅ parses empty struct
#### generic structs

- ✅ parses generic struct
- ✅ parses multi-param generic struct
#### nested structs

- ✅ parses struct with struct field
### Enum Declaration Parsing

#### simple enums

- ✅ parses enum without data
- ✅ parses enum comparison
#### enums with data

- ✅ parses enum with tuple variant
- ✅ parses enum with struct variant
#### enum matching

- ✅ parses enum in match
### Class Declaration Parsing

#### basic classes

- ✅ parses class with fields
- ✅ parses class with methods
#### class inheritance

- ✅ parses class with trait impl
### Trait Declaration Parsing

#### basic traits

- ✅ parses trait with method
- ✅ parses trait with default method
#### trait bounds

- ✅ parses trait extending trait
### Module Declaration Parsing

#### inline modules

- ✅ parses inline module
- ✅ parses nested modules
#### module items

- ✅ parses module with multiple items
### Import Declaration Parsing

- ✅ parses simple import
- ✅ parses specific import
- ✅ parses multiple imports
### Type Alias Declaration Parsing

- ✅ parses simple type alias
- ✅ parses generic type alias
- ✅ parses complex type alias
### Variable Declaration Parsing

#### immutable variables

- ✅ parses val declaration
- ✅ parses val with type annotation
#### mutable variables

- ✅ parses var declaration
- ✅ parses var with type annotation
#### let bindings

- ✅ parses let declaration
- ✅ parses let with destructuring
### Impl Block Parsing

- ✅ parses impl block for struct
- ✅ parses impl block for trait
### Attribute Declaration Parsing

- ✅ parses attribute on function
- ✅ parses attribute with args
- ✅ parses multiple attributes
- ✅ parses attribute on struct

