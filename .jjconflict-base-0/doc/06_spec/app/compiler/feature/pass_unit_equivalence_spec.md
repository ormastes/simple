# Pass Statement and Unit Value Equivalence

**Feature ID:** #LANG-021 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/pass_unit_equivalence_spec.spl`_

---

## Overview

In Simple, the `pass` keyword and the unit literal `()` are semantically
equivalent -- both represent a deliberate no-operation and compile to the same
code. This spec proves their interchangeability in every statement position:
standalone expressions, if/else branches, and loop bodies. It also documents the
style guideline that `pass` is preferred when the programmer wants to signal
explicit "do nothing" intent, while `()` is the underlying unit value.

## Syntax

```simple
# pass as a standalone no-op
pass
x = 1

# () as a standalone no-op
()
x = 1

# pass inside an if-else branch
if x == 10:
    branch_taken = "ten"
else:
    pass
    branch_taken = "other"

# pass inside a loop body
for i in [0, 1, 2]:
    if i == 1:
        pass
    count = count + 1
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `pass` | A no-op keyword signalling intentional emptiness, analogous to Python's `pass` |
| `()` | The unit literal, representing the absence of a meaningful value |
| Equivalence | `pass` and `()` produce identical compiled output in all statement positions |
| Style guideline | Use `pass` for explicit no-op intent; use `()` when a unit value is needed |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 5 |

## Test Structure

### pass and () equivalence

- ✅ both work as standalone statements
- ✅ both work in if-else branches
- ✅ both work in loops
### pass and () documentation

- ✅ documents that pass is no-op statement
### style guidelines

- ✅ recommends pass for explicit no-op intent

