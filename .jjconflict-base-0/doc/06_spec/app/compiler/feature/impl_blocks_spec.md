# Implementation Blocks Specification

**Feature ID:** #830-835 | **Category:** Language | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/impl_blocks_spec.spl`_

---

## Overview

Implementation blocks (`impl`) provide a flexible way to define methods for types outside
of the type definition. This enables separation of concerns, method organization, and
extension of types in different modules without modifying the original definition.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Impl Block | Collection of methods for a type |
| Instance Method | Methods that receive self as implicit parameter |
| Static Method | Methods that don't receive self |
| Method Organization | Grouping related behavior in impl blocks |

## Behavior

- Methods in impl blocks are part of the type's interface
- Impl blocks can be placed in any module or location
- Multiple impl blocks for the same type are merged
- Static methods are called with type name prefix
- Instance methods use dot notation on values

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 6 |

## Test Structure

### Implementation Blocks - Basic

- ✅ defines methods in impl block
- ✅ defines multiple methods
### Implementation Blocks - Static Methods

- ✅ uses static factory method
### Implementation Blocks - Instance Methods

- ✅ defines immutable methods
- ✅ defines mutable methods
### Implementation Blocks - Mixed Methods

- ✅ mixes static and instance methods

