# Null Coalescing and Try Operator Parser Specification

**Feature ID:** #PARSER-NULL-001 | **Category:** Parser / Operators | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/null_coalescing_try_operator_spec.spl`_

---

## Overview

Tests for the `??` (null coalescing) and `?` (try) operators in various contexts.
These operators should work correctly in:
- Simple expressions
- Return statements
- For loop bodies
- If expression bodies
- Match arms

## Known Issues

The following patterns cause parse errors:
1. `val x = expr ?? return Err(...)` - "expected expression, found Return"
2. `val x = expr?` inside for loop body - may cause issues
3. `val x = if cond: Some(fn()?) else: None` - "expected identifier, found Val"

## Workarounds

Use explicit if/else or match instead of operators in these contexts.

---

## Test Structure

### Null Coalescing Operator (??)
_Basic null coalescing operator tests._

#### simple expressions
- ✅ returns left value when present
- ✅ returns right value when None
- ✅ chains multiple coalescing

#### with function calls
- ✅ evaluates right side lazily
- ✅ calls right side when None

### Try Operator (?)
_Basic try operator tests._

#### with Result type
- ✅ unwraps Ok value
- ✅ propagates Err

#### with Option type
- ✅ unwraps Some value
- ✅ propagates None

### Parser Edge Cases
_Document known parser limitations with ?? and ?._

#### workaround patterns
_These patterns work correctly._

- ✅ explicit if/else instead of ?? return
- ✅ match instead of ? in for loop
- ✅ explicit match for optional config

#### previously reported bugs (now fixed)
_These patterns were reported as parser bugs but work in current bootstrap._

- ✅ ? in if-expression body
- ✅ ? in for loop with Result

#### known parser bugs _(skipped)_
- ⏭ ?? return Err pattern (skipped)
