# Method Alias Forwarding Specification

**Feature ID:** #FWD-002 | **Category:** Syntax | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/method_alias_spec.spl`_

---

## Overview

Tests that `alias fn` and `alias me` in class bodies desugar into
correct forwarding methods. The desugar transforms:
  `alias fn len = inner.len`       -> `fn len(): self.inner.len()`
  `alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)`
  `alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

These tests verify the generated delegation patterns work correctly
by writing the equivalent hand-expanded code.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### method alias forwarding

#### immutable forwarding (alias fn)

- ✅ forwards no-arg method
- ✅ forwards method with argument
- ✅ forwards zero value correctly
#### mutable forwarding (alias me)

- ✅ forwards no-arg mutable method
- ✅ forwards mutable method with argument
- ✅ chains multiple mutable forwards
#### forwarding preserves inner state

- ✅ reads after mutation reflect changes

