# Static and Const Declarations Specification

**Feature ID:** #STATIC-001 to #STATIC-015 | **Category:** Language | Declarations | **Difficulty:** 2/5 | **Status:** Planned

_Source: `test/feature/usage/static_const_declarations_spec.spl`_

---

## Overview

Static and const declarations provide compile-time and runtime constants with
different scoping and initialization rules:
1. `static val` - Module-level immutable constants with static lifetime
2. `static var` - Module-level mutable state (requires careful use)
3. `const` - Compile-time constants with inline optimization
4. `static fn` - Static methods accessible via type/module name

## Syntax

```simple
# Static value (module-level constant)
static val PI = 3.14159
static val MAX_SIZE = 1000

# Static mutable (rare, requires synchronization)
static var counter = 0

# Const (compile-time constant)
const VERSION = "1.0.0"
const DEBUG = false

# Static method
impl Math:
    static fn abs(n: i64) -> i64:
        if n < 0: -n else: n

# Static method usage
val result = Math.abs(-42)
```

## Key Concepts

| Concept | Scope | Initialization | Mutability | Use Case |
|---------|-------|-----------------|-----------|----------|
| static val | Module | Runtime | Immutable | Constants, caches |
| static var | Module | Runtime | Mutable | State, counters |
| const | Module | Compile-time | Immutable | Literals, flags |
| static fn | Type | N/A | N/A | Factory, utility |

## Behavior

- Static values are initialized once at module load
- Constants are inlined at compile time
- Static methods do not receive `self` parameter
- Static var requires thread-safe access in concurrent contexts
- Statics are lazily initialized (first access)

## Related Specifications

- [Module System](module_system_spec.spl) - Scoping rules
- [Functions](functions_spec.spl) - Method definitions

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 53 |

## Test Structure

### Static Value Declaration

- ✅ parses simple static value
- ✅ parses static value with type annotation
- ✅ parses static value with complex expression
- ✅ parses multiple static values

