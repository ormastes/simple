# CompilerServices Error Cases

**Feature ID:** #BACKEND-002 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/app/compiler_services_error_cases_spec.spl`_

---

## Overview

Tests failure paths and edge cases for noop port behavior in CompilerServices. Validates that
noop ports handle degenerate inputs gracefully, including empty strings, empty lists, and
nonexistent paths. Verifies idempotency of repeated calls, that the noop logger does not crash
on empty messages, that the noop module loader returns sensible defaults, and that the noop
desugarer passes input through unchanged. Also confirms independent factory instances.

## Syntax

```simple
val svc = create_default_services()
val f = svc.lexer.tokenize_fn
val result = f("")
expect(result.len()).to_equal(0)

val rf = svc.module_loader.resolve_fn
val result = rf("/src/main.spl", "std.string")
expect(result).to_equal("std.string")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 33 |

## Test Structure

### CompilerServices Error Cases: noop lexer degenerate inputs

- ✅ tokenize empty string returns empty list
- ✅ tokenize whitespace-only input returns empty list
- ✅ tokenize any input always returns empty list for noop
- ✅ calling tokenize twice is idempotent
### CompilerServices Error Cases: noop parser degenerate inputs

- ✅ parse empty token list with empty source returns no errors
- ✅ parse non-empty token list with empty source returns no errors
- ✅ parse empty token list with non-empty source returns no errors
- ✅ calling parse twice returns empty errors both times
### CompilerServices Error Cases: noop desugarer edge cases

- ✅ desugar empty string returns empty string
- ✅ desugar whitespace-only returns whitespace unchanged
- ✅ desugar returns input text unchanged for noop
- ✅ calling desugar twice returns same result
### CompilerServices Error Cases: noop type checker degenerate inputs

- ✅ check empty module name returns no errors
- ✅ check nonexistent module name returns no errors for noop
- ✅ calling check multiple times returns empty each time
### CompilerServices Error Cases: noop HIR lowerer degenerate inputs

- ✅ lower empty module name returns no errors
- ✅ lower nonexistent module returns no errors for noop
### CompilerServices Error Cases: noop MIR lowerer degenerate inputs

- ✅ lower empty module name returns no errors
- ✅ lower any module returns no errors for noop
### CompilerServices Error Cases: noop logger degenerate inputs

- ✅ info_fn does not crash on empty message
- ✅ debug_fn does not crash on empty message
- ✅ warn_fn does not crash on empty message
- ✅ error_fn does not crash on empty message
- ✅ calling all log levels in sequence does not crash
### CompilerServices Error Cases: noop module loader degenerate inputs

- ✅ load_fn returns empty string for nonexistent path
- ✅ load_fn returns empty string for empty path
- ✅ resolve_fn returns import name unchanged for noop
- ✅ resolve_fn returns empty string for empty import name
- ✅ resolve_fn with both empty args returns empty string
### CompilerServices Error Cases: noop backend degenerate inputs

- ✅ supports_jit_fn always returns false for noop
- ✅ target_triple_fn always returns noop for noop backend
### CompilerServices Error Cases: independent factory instances

- ✅ two factory calls produce independent services
- ✅ noop services from different factory calls return same results

