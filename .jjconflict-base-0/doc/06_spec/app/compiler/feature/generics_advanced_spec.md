# Advanced Generics Specification

**Feature ID:** #GEN-ADV-001 to #GEN-ADV-008 | **Category:** Type System | Generics | **Status:** Implemented

_Source: `test/feature/usage/generics_advanced_spec.spl`_

---

## Syntax

```simple
# Const generics
struct Array<T, const N: usize>:
    data: T

# Where clause
fn filled(value: T) -> T where T: Copy:
    value

# impl Trait for Type
impl Len for MyList:
    fn len() -> i64:
        self.size

# Multiple trait bounds
fn make<T>() -> T where T: Clone + Default:
    T.default()

# Associated types
trait Iterator:
    type Item
    fn next() -> Option<Self.Item>
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Const Generic Parameters

- ✅ parses const generic parameter
### Where Clauses

- ✅ parses where clause on function
### impl Trait for Type

- ✅ parses impl trait for type
### Generic impl with Where

- ✅ parses generic impl with where
### Nested Generic Types

- ✅ parses nested generic types
### Tuple Return Types

- ✅ parses tuple return type
### Multiple Trait Bounds

- ✅ parses multiple trait bounds
### Associated Types

- ✅ parses associated type

