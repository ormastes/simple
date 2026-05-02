# Implicit Context Parameters

**Feature ID:** #CTX-001 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/implicit_context_spec.spl`_

---

## Overview

Tests implicit context parameters declared with `context val` and bound with
`with_context`. Verifies that context variables work as module-level state
shared across all functions, that nested function calls share the same context,
that context can be swapped between loggers, and that the save-set-restore
pattern correctly preserves outer context after inner scope execution.

## Syntax

```simple
context val logger: TestLogger
with_context(logger: inner_logger):
    _lex("x")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Feature 7: Implicit Context Parameters

- ✅ context variable is accessible in functions
- ✅ functions share the same context variable
- ✅ last logged message is from deepest function call
- ✅ context variable can be swapped for different loggers
- ✅ save-set-restore pattern preserves outer context
- ✅ nil context is default before any with_context
### Feature 7: Multiple Context Variables

- ✅ multiple context vars are independent
- ✅ setting one ctx var does not affect others

