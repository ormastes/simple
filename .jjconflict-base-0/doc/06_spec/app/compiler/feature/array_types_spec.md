# Array Type System and Operations

**Feature ID:** #LANG-003 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/array_types_spec.spl`_

---

## Overview

Arrays are Simple's primary ordered collection type, supporting literal construction,
positive and negative indexing, slicing with `start:end:step` notation, and a full suite
of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive
spec covers eight aspects of array behavior: basic creation and queries, mutation via `push`
and `concat`, functional transformations, Python-style slicing, negative indexing, the
spread operator (`*`) for array merging, list comprehensions with optional filter clauses,
and chained comparison expressions.

## Syntax

```simple
val arr = [1, 2, 3, 4, 5]
val doubled = arr.map(\x: x * 2)
val sub = arr[1:4]
val evens = [x for x in arr if x % 2 == 0]
val merged = [*a, *b]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Array Literal | `[1, 2, 3]` creates a dynamic array with inferred element type |
| Slicing | `arr[start:end:step]` extracts sub-arrays using Python-style notation |
| Spread Operator | `[*a, *b]` unpacks arrays inline to build a new merged array |
| List Comprehension | `[expr for x in iter if cond]` builds arrays with inline loops and filters |
| Functional Methods | `map`, `filter`, `reduce`, `all`, `join`, `sum` for declarative transforms |
| Negative Indexing | `arr[-1]` accesses elements from the end of the array |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 30 |

## Test Structure

### Array Basics

#### array literals

- ✅ creates array from literal
- ✅ gets array length
- ✅ gets first and last elements
#### array queries

- ✅ checks if array contains element
- ✅ checks if array is empty
- ✅ checks non-empty array
### Array Modification

#### push and concat

- ✅ pushes element to array
- ✅ concatenates two arrays
#### reverse

- ✅ reverses array
### Array Functional Methods

#### map

- ✅ maps function over array
#### filter

- ✅ filters array by predicate
#### reduce

- ✅ reduces array with accumulator
#### all and any

- ✅ checks all elements match predicate
#### join

- ✅ joins array elements with separator
#### sum

- ✅ sums numeric array
### Array Slicing

#### basic slicing

- ✅ slices with start and end
- ✅ slices from start index to end
- ✅ slices from beginning to end index
#### step slicing

- ✅ slices with step
### Negative Indexing

- ✅ gets last element with -1
- ✅ gets second from end with -2
### Array Spread Operator

- ✅ spreads arrays with *
- ✅ spreads array mixed with elements
### List Comprehension

- ✅ creates list from comprehension
- ✅ filters with comprehension condition
- ✅ creates squares with comprehension
### Chained Comparisons

- ✅ evaluates basic chained comparison
- ✅ evaluates false chained comparison
- ✅ evaluates three-way comparison
- ✅ evaluates mixed comparison operators

