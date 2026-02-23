# Macro Hygiene Specification

**Feature ID:** #MACRO-001 | **Category:** Language | Macros | **Status:** Implemented

_Source: `test/feature/usage/macro_hygiene_spec.spl`_

---

## Overview

Tests for macro hygiene system that prevents variable capture through
gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness,
and pattern matching with hygiene.

## Syntax

```simple
macro make_ten() -> (returns result: Int):
    emit result:
        val x = 10
        x

val x = 5
val result = make_ten!()
# x is still 5, result is 10
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Basic Macro Hygiene

- ✅ prevents variable capture
- ✅ isolates macro internal variables
- ✅ preserves outer variable after macro
### Nested Scope Hygiene

- ✅ handles nested scopes in macro
- ✅ handles nested macro calls
- ✅ handles nested blocks
### Gensym Uniqueness

- ✅ creates unique names across calls
- ✅ gensyms multiple variables
### Pattern Matching Hygiene

- ✅ isolates pattern variables
- ✅ isolates tuple destructuring
- ✅ isolates array destructuring
### Function Parameter Hygiene

- ✅ isolates function parameters
- ✅ isolates function from outer scope
- ✅ handles nested functions
### Complex Macro Hygiene

- ✅ handles complex multi-scope macro
- ✅ handles macro parameters
- ✅ handles nested macros with same names
### Macro Hygiene Edge Cases

- ✅ handles empty macro
- ✅ handles macro with early return
- ✅ handles variable shadowing

