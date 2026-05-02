# AOP Pointcut Expression Specification

**Feature ID:** #AOP-PC-001 to #AOP-PC-015 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/aop_pointcut_spec.spl`_

---

## Syntax

```simple
pc{ selector(pattern) }
pc{ selector1(...) & selector2(...) }  # AND
pc{ selector1(...) | selector2(...) }  # OR
pc{ !selector(...) }                   # NOT
```

## Selectors

| Selector | Description | Example |
|----------|-------------|---------|
| execution | Match function execution | `execution(* foo(..))` |
| within | Match code in module/class | `within(services.*)` |
| attr | Match by attribute | `attr(logged)` |

## Limitations (Current Implementation)

- Init selector not yet implemented (requires around advice)
- Inline module definitions in test blocks not supported

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 12 |

## Test Structure

### Execution Pointcut Selector

#### return type patterns

- ✅ matches any return type with wildcard
#### function name patterns

- ✅ matches exact function name
- ✅ matches prefix wildcard
- ✅ matches suffix wildcard
#### parameter patterns

- ✅ matches any parameters with (..)
### Attribute Pointcut Selector

#### function attributes

- ✅ matches function with attribute
- ✅ matches multiple attributes
### Pointcut Logical Operators

#### AND operator

- ✅ requires both conditions
#### OR operator

- ✅ matches either condition
#### NOT operator

- ✅ excludes matching pointcuts
### Wildcard Patterns in Pointcuts

#### prefix and suffix wildcards

- ✅ matches prefix with name*
- ✅ matches suffix with *name

