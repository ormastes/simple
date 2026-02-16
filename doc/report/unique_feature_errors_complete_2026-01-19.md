# Unique Feature Error Codes - Completion Report

**Date:** 2026-01-19
**Status:** Complete
**Total New Error Codes:** 48

## Summary

Added comprehensive error codes for Simple language's unique features that differentiate it from other programming languages:

1. **AOP (Aspect-Oriented Programming)** - E15xx series
2. **Custom Blocks** (m{}, sh{}, sql{}, re{}, etc.) - E16xx series
3. **Mixins** - E17xx series
4. **SDN (Self-Describing Notation)** - E18xx series
5. **DI (Dependency Injection)** - E19xx series
6. **Architecture Rules** - E1Axx series

## Files Modified

### Rust Source Code
- `src/compiler/src/error.rs` - Added 48 error code constants

### i18n Files
- `src/i18n/__init__.spl` - English error messages (192 new lines)
- `src/i18n/__init__.ko.spl` - Korean translations (192 new lines)
- `src/i18n/compiler.spl` - Catalog entries (360 new lines)

### BDD Test Specifications
- `simple/std_lib/test/features/errors/aop_errors_spec.spl`
- `simple/std_lib/test/features/errors/custom_block_errors_spec.spl`
- `simple/std_lib/test/features/errors/mixin_errors_spec.spl`
- `simple/std_lib/test/features/errors/sdn_errors_spec.spl`
- `simple/std_lib/test/features/errors/di_errors_spec.spl`
- `simple/std_lib/test/features/errors/arch_errors_spec.spl`

### Documentation
- `doc/plan/unique_feature_error_codes_plan.md` - Implementation plan

## Error Code Details

### E15xx - AOP Errors (8 codes)
| Code | Name | Description |
|------|------|-------------|
| E1501 | INVALID_POINTCUT_SYNTAX | Invalid `pc{...}` pointcut expression syntax |
| E1502 | UNDEFINED_JOINPOINT | Referenced join point does not exist |
| E1503 | INVALID_ADVICE_TYPE | Invalid advice type (before/after_success/after_error/around) |
| E1504 | CONFLICTING_ADVICE_ORDER | Multiple advices with conflicting execution order |
| E1505 | INVALID_WEAVING_TARGET | Target cannot be woven (intrinsic, FFI) |
| E1506 | ASPECT_CIRCULAR_DEPENDENCY | Circular dependency between aspects |
| E1507 | INVALID_POINTCUT_SELECTOR | Unknown selector (execution/within/attr/effect) |
| E1508 | ASPECT_NOT_ENABLED | Aspect used but not enabled in configuration |

### E16xx - Custom Block Errors (12 codes)
| Code | Name | Description |
|------|------|-------------|
| E1601 | UNKNOWN_BLOCK_TYPE | Unknown custom block type |
| E1602 | INVALID_BLOCK_SYNTAX | Syntax error within custom block |
| E1603 | MATH_BLOCK_INVALID_EXPR | Invalid mathematical expression in m{} |
| E1604 | MATH_BLOCK_UNDEFINED_VAR | Undefined variable in math block |
| E1605 | SHELL_BLOCK_INVALID_CMD | Invalid command in sh{} block |
| E1606 | SHELL_BLOCK_UNSAFE_OP | Unsafe operation in shell block |
| E1607 | SQL_BLOCK_SYNTAX_ERROR | SQL syntax error in sql{} block |
| E1608 | SQL_BLOCK_INVALID_PARAM | Invalid parameter in SQL block |
| E1609 | REGEX_BLOCK_INVALID | Invalid regular expression in re{} |
| E1610 | REGEX_BLOCK_UNKNOWN_FLAG | Unknown regex flag |
| E1611 | BLOCK_MISSING_CLOSING | Missing closing brace |
| E1612 | BLOCK_TYPE_MISMATCH | Content doesn't match block type |

### E17xx - Mixin Errors (8 codes)
| Code | Name | Description |
|------|------|-------------|
| E1701 | MIXIN_NOT_FOUND | Referenced mixin does not exist |
| E1702 | MIXIN_METHOD_CONFLICT | Conflicting methods from mixins |
| E1703 | MIXIN_MISSING_REQUIRED | Missing required method implementation |
| E1704 | MIXIN_CIRCULAR_DEPENDENCY | Circular mixin dependency |
| E1705 | MIXIN_INVALID_USE | Invalid `use` statement |
| E1706 | MIXIN_FIELD_CONFLICT | Conflicting fields from mixins |
| E1707 | MIXIN_SELF_REFERENCE | Mixin references itself |
| E1708 | MIXIN_TYPE_MISMATCH | Type parameter mismatch |

### E18xx - SDN Errors (8 codes)
| Code | Name | Description |
|------|------|-------------|
| E1801 | SDN_SYNTAX_ERROR | Invalid SDN syntax |
| E1802 | SDN_UNKNOWN_KEY | Unknown configuration key |
| E1803 | SDN_TYPE_MISMATCH | Value type mismatch |
| E1804 | SDN_MISSING_REQUIRED | Missing required key |
| E1805 | SDN_DUPLICATE_KEY | Duplicate key in block |
| E1806 | SDN_INVALID_VALUE | Invalid value for key |
| E1807 | SDN_NESTING_LIMIT | Nesting depth limit exceeded |
| E1808 | SDN_CIRCULAR_REFERENCE | Circular reference in config |

### E19xx - DI Errors (8 codes)
| Code | Name | Description |
|------|------|-------------|
| E1901 | DI_MISSING_BINDING | No binding for required type |
| E1902 | DI_AMBIGUOUS_BINDING | Multiple bindings match |
| E1903 | DI_CIRCULAR_DEPENDENCY | Circular DI dependency |
| E1904 | DI_INVALID_SCOPE | Invalid scope annotation |
| E1905 | DI_INJECT_FAILED | Injection failed at runtime |
| E1906 | DI_INVALID_ATTRIBUTE | Invalid @sys.inject usage |
| E1907 | DI_SCOPE_MISMATCH | Singleton depends on Transient |
| E1908 | DI_MOCK_NOT_TEST | Mock binding outside test |

### E1Axx - Architecture Rule Errors (6 codes)
| Code | Name | Description |
|------|------|-------------|
| E1A01 | ARCH_FORBIDDEN_IMPORT | Import violates architecture rule |
| E1A02 | ARCH_FORBIDDEN_DEPEND | Dependency violates rule |
| E1A03 | ARCH_LAYER_VIOLATION | Cross-layer dependency violation |
| E1A04 | ARCH_INVALID_RULE | Invalid rule syntax |
| E1A05 | ARCH_CONFLICTING_RULES | Conflicting forbid/allow rules |
| E1A06 | ARCH_CIRCULAR_MODULES | Circular module dependency |

## i18n Coverage

All 48 error codes have:
- English messages with title, message, label, and help
- Korean translations (100% coverage)
- Catalog entries for runtime lookup

## BDD Test Coverage

Each feature area has a dedicated spec file with:
- Describe blocks for each error code
- Context blocks for error scenarios
- Korean language verification tests
- Documentation in SSpec format

## Verification

```bash
$ cargo check --package simple-compiler
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 5.09s
```

All code compiles successfully with no errors or warnings.

## Next Steps

1. Wire up error codes to actual compiler phases (parsing, semantic analysis)
2. Add runtime error generation for DI and architecture rule violations
3. Create user documentation for each error code
4. Add `--explain E1501` style help output
