# Dictionary Types Specification

**Feature ID:** #1002 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/dictionary_types_spec.spl`_

---

use std.text.{NL}

Tests for dictionary (map) types and their operations.
Verifies dictionary creation, access, modification, and iteration.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Dictionary Types

#### dictionary creation

- ✅ creates empty dictionary
- ✅ creates dictionary with initial values
- ✅ creates dictionary with string keys and values
#### dictionary access

- ✅ retrieves value by key
- ✅ returns null for missing key
- ✅ checks key existence
#### dictionary modification

- ✅ adds new key-value pair
- ✅ updates existing value
- ✅ removes entry by key
#### dictionary iteration

- ✅ iterates over keys
- ✅ iterates over values
- ✅ iterates over entries
#### dictionary methods

- ✅ gets dictionary size
- ✅ checks if dictionary is empty
- ✅ clears dictionary
- ✅ creates copy of dictionary
#### dictionary with multiple types

- ✅ stores different value types
- ✅ accesses values with correct types
### Functional Dictionary Methods

#### set and merge

- ✅ sets key with functional update
- ✅ merges two dictionaries
#### get with default

- ✅ gets value or default
- ✅ gets existing value instead of default
### Dictionary Comprehension

- ✅ creates dict from comprehension

