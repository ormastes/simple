# Advanced Operators Specification

**Feature ID:** #OP-ADV-001 to #OP-ADV-030 | **Category:** Language | Operators | **Status:** Implemented

_Source: `test/feature/usage/operators_advanced_spec.spl`_

---

## Syntax

```simple
# Mutability
let x = 10       # immutable
let mut y = 10   # mutable with let mut
var z = 10       # mutable with var
const MAX = 100  # constant
static counter = 0  # static variable

# Operators
val a = 12 & 10    # bitwise AND
val b = 2 ** 10    # power
val c = 7.fdiv(2)  # floor division (// is now parallel operator)
val d = "ell" in "hello"  # in operator
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 52 |

## Test Structure

### Mutability Control

- ✅ let is immutable
- ✅ var is mutable
- ✅ var in loop
- ✅ const declaration
- ✅ const with arithmetic
- ✅ const with type annotation
- ✅ static variable
### Lambda Expressions

- ✅ basic lambda
- ✅ lambda with multiple params
- ✅ lambda as higher-order
### String Operations

- ✅ string length
- ✅ string concatenation
- ✅ string interpolation
### Array Methods

- ✅ array length
### Dict Methods

- ✅ dict length
- ✅ dict keys
- ✅ dict values
- ✅ dict contains_key
### Bitwise Operators

- ✅ bitwise AND
- ✅ bitwise OR
- ✅ bitwise XOR
- ✅ left shift
- ✅ right shift
- ✅ bitwise NOT
### Comparison Operators

- ✅ less than
- ✅ greater than
- ✅ less than or equal
- ✅ greater than or equal
- ✅ equal
- ✅ not equal
### Logical Operators

- ✅ and operator
- ✅ or operator
- ✅ not operator
### Power Operator

- ✅ power of zero
- ✅ power of one
- ✅ power of three
- ✅ power of ten
- ✅ three to fourth
### Floor Division

- ✅ positive floor division
- ✅ another floor division
- ✅ negative floor division
- ✅ exact division
### In Operator

- ✅ in array present
- ✅ in array absent
- ✅ in string present
- ✅ in string absent
### Recursive Functions

- ✅ factorial
### Nested Data Structures

- ✅ nested arrays
- ✅ nested structs
### Early Return

- ✅ early return based on condition
### Tuple Destructuring

- ✅ destructures tuple
### Symbols

- ✅ symbol comparison

