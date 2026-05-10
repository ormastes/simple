# Context Managers Specification

**Feature ID:** #CONTEXT-MANAGER | **Category:** Language | **Status:** Implemented

_Source: `test/feature/usage/context_managers_spec.spl`_

---

## Syntax

```simple
with resource as alias:
    # code using alias
    # __exit__ is called after this block
```

## Key Behaviors

- `__enter__()` is called on entry, its return value is bound to alias
- `__exit__()` is always called, even if an exception occurs
- Alias binding can coexist with parser special handling (e.g., cast expressions)
- Clean separation between resource acquisition and usage
- Exception safety: cleanup always happens

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 14 |

## Test Structure

### Context Managers

#### basic context manager protocol

- ✅ calls __enter__ and binds result to alias
- ✅ calls __exit__ after block completes
#### alias binding and reuse

- ✅ reuses identifier when parser sees cast-style syntax
- ✅ properly binds alias in nested contexts
#### resource cleanup

- ✅ runs cleanup code after block
- ✅ runs cleanup even after multiple operations
#### using acquired values

- ✅ can use alias from __enter__ return value
- ✅ can call methods on alias
#### exception handling

- ✅ passes exception info to __exit__
- ✅ always calls __exit__ for resource cleanup
#### multiple resources

- ✅ can nest multiple context managers
- ✅ cleans up in reverse order
#### practical patterns

- ✅ implements file-like resource pattern
- ✅ ensures state is restored on exit

