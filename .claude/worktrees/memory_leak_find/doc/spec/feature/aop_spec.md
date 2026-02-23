# Aspect-Oriented Programming (AOP) Specification

**Feature ID:** #AOP-001 to #AOP-020 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/aop_spec.spl`_

---

## Syntax

```simple
# Before advice - runs before target function
on pc{ execution(* target_func(..)) } use advice_func before priority 10

# After advice - runs after successful execution
on pc{ execution(* target_func(..)) } use advice_func after_success priority 5

# Architecture rules
forbid pc{ import(test.internal.*) } "Production cannot import test internals"
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Advice | Code that executes at join points (before/after/around) |
| Pointcut | Expression defining where advice applies: `pc{...}` |
| Join point | Execution point where advice can be woven |
| Weaving | Process of inserting advice at join points |
| Priority | Integer controlling advice execution order |

## Behaviors

- Higher priority executes earlier for `before` advice
- Higher priority executes later for `after_*` advice
- `around` advice must call `proceed()` exactly once
- Zero overhead when AOP is not enabled
- Compile-time weaving for `before`/`after`, runtime for `around`

## Limitations (Current Implementation)

- Around advice not yet implemented (skipped tests)
- Inline module definitions in test blocks not supported
- DI integration not yet implemented (skipped tests)

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### AOP Basic Syntax

#### before advice declaration

- ✅ parses before advice with execution pointcut
- ✅ parses before advice with wildcard return type
#### after advice declaration

- ✅ parses after_success advice
- ✅ parses after_error advice
### Before Advice Execution

#### execution order

- ✅ executes before advice before target
### After Advice Execution

#### after_success execution

- ✅ executes after_success when target succeeds
- ✅ does not execute after_success when target returns Err
#### after_error execution

- ✅ executes after_error when target returns Err
### Pointcut Expressions

#### execution patterns

- ✅ matches specific function name
- ✅ matches with wildcard in function name
#### attribute patterns

- ✅ matches functions with specific attribute
#### logical operators

- ✅ combines pointcuts with AND
- ✅ combines pointcuts with OR
- ✅ negates pointcuts with NOT
### Architecture Rules

#### forbid rules

- ✅ declares forbidden import pattern
- ✅ declares forbidden dependency pattern
#### allow rules

- ✅ declares allowed dependency pattern
### Weaving Diagnostics

#### weaving reports

- ✅ reports join points woven
- ✅ validates advice configuration
### Zero Overhead When Disabled

#### no advice means no overhead

- ✅ function without advice has no weaving
- ✅ disabled weaving produces no diagnostics

