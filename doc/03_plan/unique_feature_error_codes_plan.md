# Unique Feature Error Codes Plan

**Date:** 2026-01-19
**Status:** Complete
**Author:** Claude Code

## Overview

This document plans error codes for Simple language's unique features that differentiate it from other programming languages. The goal is to add comprehensive error codes with i18n support (English + Korean) and BDD test specifications.

## Unique Features Requiring Error Codes

| Feature | Error Code Range | Current Status |
|---------|------------------|----------------|
| AOP (Aspect-Oriented Programming) | E15xx | Missing |
| Custom Blocks (m{}, sh{}, sql{}, re{}) | E16xx | Missing |
| Mixins | E17xx | Missing |
| SDN (Self-Describing Notation) | E18xx | Missing |
| DI (Dependency Injection) | E19xx | Missing |
| Architecture Rules | E1Axx | Missing |

## Error Code Allocations

### E15xx - AOP Errors

| Code | Name | Description |
|------|------|-------------|
| E1501 | INVALID_POINTCUT_SYNTAX | Invalid `pc{...}` pointcut expression syntax |
| E1502 | UNDEFINED_JOINPOINT | Referenced join point does not exist |
| E1503 | INVALID_ADVICE_TYPE | Invalid advice type (must be before/after_success/after_error/around) |
| E1504 | CONFLICTING_ADVICE_ORDER | Multiple advices with conflicting execution order |
| E1505 | INVALID_WEAVING_TARGET | Target cannot be woven (e.g., intrinsic, FFI) |
| E1506 | ASPECT_CIRCULAR_DEPENDENCY | Circular dependency between aspects |
| E1507 | INVALID_POINTCUT_SELECTOR | Unknown selector in pointcut (execution/within/attr/effect) |
| E1508 | ASPECT_NOT_ENABLED | Aspect used but not enabled in configuration |

### E16xx - Custom Block Errors

| Code | Name | Description |
|------|------|-------------|
| E1601 | UNKNOWN_BLOCK_TYPE | Unknown custom block type (not m/sh/sql/re/md/html/graph/img) |
| E1602 | INVALID_BLOCK_SYNTAX | Syntax error within custom block |
| E1603 | MATH_BLOCK_INVALID_EXPR | Invalid mathematical expression in `m{}` block |
| E1604 | MATH_BLOCK_UNDEFINED_VAR | Undefined variable in math block |
| E1605 | SHELL_BLOCK_INVALID_CMD | Invalid or unsupported command in `sh{}` block |
| E1606 | SHELL_BLOCK_UNSAFE_OP | Potentially unsafe operation in shell block |
| E1607 | SQL_BLOCK_SYNTAX_ERROR | SQL syntax error in `sql{}` block |
| E1608 | SQL_BLOCK_INVALID_PARAM | Invalid parameter in SQL block |
| E1609 | REGEX_BLOCK_INVALID | Invalid regular expression in `re{}` block |
| E1610 | REGEX_BLOCK_UNKNOWN_FLAG | Unknown regex flag |
| E1611 | BLOCK_MISSING_CLOSING | Missing closing brace for custom block |
| E1612 | BLOCK_TYPE_MISMATCH | Block content doesn't match expected type |

### E17xx - Mixin Errors

| Code | Name | Description |
|------|------|-------------|
| E1701 | MIXIN_NOT_FOUND | Referenced mixin does not exist |
| E1702 | MIXIN_METHOD_CONFLICT | Conflicting method definitions from multiple mixins |
| E1703 | MIXIN_MISSING_REQUIRED | Missing required method implementation for mixin |
| E1704 | MIXIN_CIRCULAR_DEPENDENCY | Circular dependency between mixins |
| E1705 | MIXIN_INVALID_USE | Invalid `use` statement for mixin |
| E1706 | MIXIN_FIELD_CONFLICT | Conflicting field definitions from mixins |
| E1707 | MIXIN_SELF_REFERENCE | Mixin cannot reference itself |
| E1708 | MIXIN_TYPE_MISMATCH | Mixin type parameter mismatch |

### E18xx - SDN (Self-Describing Notation) Errors

| Code | Name | Description |
|------|------|-------------|
| E1801 | SDN_SYNTAX_ERROR | Invalid SDN syntax |
| E1802 | SDN_UNKNOWN_KEY | Unknown key in SDN configuration |
| E1803 | SDN_TYPE_MISMATCH | Value type doesn't match expected type |
| E1804 | SDN_MISSING_REQUIRED | Missing required key in SDN |
| E1805 | SDN_DUPLICATE_KEY | Duplicate key in SDN block |
| E1806 | SDN_INVALID_VALUE | Invalid value for SDN key |
| E1807 | SDN_NESTING_LIMIT | SDN nesting depth limit exceeded |
| E1808 | SDN_CIRCULAR_REFERENCE | Circular reference in SDN |

### E19xx - DI (Dependency Injection) Errors

| Code | Name | Description |
|------|------|-------------|
| E1901 | DI_MISSING_BINDING | No binding found for required dependency |
| E1902 | DI_AMBIGUOUS_BINDING | Multiple bindings match (ambiguous resolution) |
| E1903 | DI_CIRCULAR_DEPENDENCY | Circular dependency in DI graph |
| E1904 | DI_INVALID_SCOPE | Invalid scope annotation (must be Singleton/Transient) |
| E1905 | DI_INJECT_FAILED | Dependency injection failed at runtime |
| E1906 | DI_INVALID_ATTRIBUTE | Invalid `@sys.inject` attribute usage |
| E1907 | DI_SCOPE_MISMATCH | Singleton depends on Transient (scope violation) |
| E1908 | DI_MOCK_NOT_TEST | Mock binding used outside test context |

### E1Axx - Architecture Rule Errors

| Code | Name | Description |
|------|------|-------------|
| E1A01 | ARCH_FORBIDDEN_IMPORT | Import violates architecture rule |
| E1A02 | ARCH_FORBIDDEN_DEPEND | Dependency violates architecture rule |
| E1A03 | ARCH_LAYER_VIOLATION | Cross-layer dependency violation |
| E1A04 | ARCH_INVALID_RULE | Invalid architecture rule syntax |
| E1A05 | ARCH_CONFLICTING_RULES | Conflicting forbid/allow rules |
| E1A06 | ARCH_CIRCULAR_MODULES | Circular module dependency |

## BDD Test Specifications

Each error code will have BDD tests covering:
1. **Basic Case** - Standard error triggering scenario
2. **Edge Cases** - Boundary conditions
3. **Korean Language** - i18n verification

### Test File Structure

```
simple/std_lib/test/features/errors/
├── aop_errors_spec.spl          # E15xx
├── custom_block_errors_spec.spl # E16xx
├── mixin_errors_spec.spl        # E17xx
├── sdn_errors_spec.spl          # E18xx
├── di_errors_spec.spl           # E19xx
└── arch_errors_spec.spl         # E1Axx
```

## Implementation Order

1. **Phase 1: Error Codes** - Add codes to `src/compiler/src/error.rs`
2. **Phase 2: i18n Messages** - Add to `src/i18n/__init__.spl` and `src/i18n/__init__.ko.spl`
3. **Phase 3: Catalog** - Add to `src/i18n/compiler.spl`
4. **Phase 4: BDD Tests** - Create spec files

## Example Error Messages

### E1501 - INVALID_POINTCUT_SYNTAX
```
error[E1501]: invalid pointcut syntax
  --> src/aspects/logging.spl:5:8
   |
 5 |     pc{execution( missing closing}
   |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected ')' after function pattern
   |
help: close the function pattern with ')'
```

### E1701 - MIXIN_NOT_FOUND
```
error[E1701]: mixin not found
  --> src/models/user.spl:3:5
   |
 3 |     use Serializable
   |         ^^^^^^^^^^^^ mixin 'Serializable' is not defined
   |
help: did you mean 'Serialize'?
note: available mixins: Serialize, Validate, Loggable
```

### E1901 - DI_MISSING_BINDING
```
error[E1901]: missing binding for dependency
  --> src/services/auth.spl:10:20
   |
10 |     @sys.inject
11 |     val db: Database
   |             ^^^^^^^^ no binding registered for type 'Database'
   |
help: register a binding in your DI configuration
note: use 'bind Database = SqliteDatabase' in your module
```

## Success Criteria

- [x] All 48 error codes added to `error.rs`
- [x] English messages in `src/i18n/__init__.spl`
- [x] Korean translations in `src/i18n/__init__.ko.spl`
- [x] Catalog entries in `src/i18n/compiler.spl`
- [x] 6 BDD spec files with 3+ scenarios per error code
- [x] Code compiles successfully
