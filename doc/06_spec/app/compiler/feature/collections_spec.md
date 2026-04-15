# Collections Specification

**Feature ID:** #COLLECTIONS-001 | **Category:** Language | Collections | **Status:** Implemented

_Source: `test/feature/usage/collections_spec.spl`_

---

## Overview

Tests for collection types including arrays, tuples, dictionaries, and strings.
Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## Syntax

```simple
val arr = [1, 2, 3]                    # Array literal
val t = (10, 20, 30)                   # Tuple literal
val d = {"a": 1, "b": 2}               # Dictionary literal
val doubled = arr.map(\x: x * 2)       # Functional method
val squares = [x * x for x in arr]    # List comprehension
val sub = arr[1:4]                     # Slicing
val last = arr[-1]                     # Negative indexing
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 54 |

## Test Structure

### Array Basics

- ✅ creates array literal and accesses by index
- ✅ gets array length
- ✅ gets first and last elements
- ✅ checks if array contains element
- ✅ checks if array is empty
### Tuple Basics

- ✅ creates tuple literal and accesses by index
- ✅ gets tuple length
- ✅ destructures tuple
### Dictionary Basics

- ✅ creates dict literal and accesses by key
- ✅ gets dict length
- ✅ checks if dict contains key
- ✅ gets value from dict
### String Operations

- ✅ gets string length
- ✅ checks if string contains substring
- ✅ indexes string to get character
### Array Mutation Methods

- ✅ pushes element to array
- ✅ concatenates two arrays
- ✅ slices array
### Array Functional Methods

- ✅ maps array elements
- ✅ filters array elements
- ✅ reduces array to single value
- ✅ checks all elements match predicate
- ✅ joins array elements to string
- ✅ sums array elements
- ✅ reverses array
### Dictionary Methods

- ✅ sets new key in dict
- ✅ removes key from dict
- ✅ merges two dicts
- ✅ gets with default value
### List Comprehension

- ✅ creates list with basic comprehension
- ✅ creates list with condition
- ✅ creates squares list
### Dict Comprehension

- ✅ creates dict with comprehension
### Slicing

- ✅ slices with start and end
- ✅ slices from start index to end
- ✅ slices from beginning to end index
- ✅ slices with step
### Negative Indexing

- ✅ accesses last element with -1
- ✅ accesses second from end with -2
- ✅ accesses string with negative index
### Spread Operators

- ✅ spreads two arrays
- ✅ spreads with mixed elements
### Tuple Unpacking

- ✅ unpacks basic tuple
- ✅ unpacks with swap pattern
- ✅ unpacks array to tuple
### Chained Comparisons

- ✅ evaluates basic chained comparison
- ✅ evaluates false chained comparison
- ✅ evaluates three-way comparison
- ✅ evaluates mixed comparison operators
### Context Managers

- ✅ executes basic with block
- ✅ binds resource with as
- ✅ calls __enter__ and __exit__ on class
### Decorators

- ✅ applies basic decorator
- ✅ applies decorator with arguments

