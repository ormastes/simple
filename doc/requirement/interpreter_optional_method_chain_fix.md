# Interpreter Optional Method Chain Fix — Requirements

**Feature:** Fix interpreter bugs INTERP-CHAIN-001 and INTERP-DICT-002
**Date:** 2026-03-15
**Type:** Bugfix
**Component:** Interpreter (Rust)

## Motivation

Two interpreter bugs prevent idiomatic Simple code from working:

1. **Chained method on unwrapped enum** (INTERP-CHAIN-001): `optional_enum.unwrap().method()` fails because the interpreter loses the concrete enum type after `.unwrap()`, tagging it as generic `enum`.

2. **Dict.get() auto-unwrap** (INTERP-DICT-002): `Dict<K,V>.get(key)` returns the raw value instead of `V?` (optional) when the key exists, causing `.unwrap()` to fail with "method not found on type str".

## Scope

### In Scope
- Fix interpreter method dispatch to preserve concrete enum type through `.unwrap()` chains
- Fix `Dict.get()` to consistently return `Optional<V>` rather than auto-unwrapping
- Intensive regression tests covering optional/method-chain edge cases

### Out of Scope
- Compiler-mode fixes (these bugs are interpreter-only)
- Other chained method issues beyond optional unwrap

## Acceptance Criteria

1. `TypeDefault.from_text("i32").unwrap().to_text()` returns `"i32"` without error
2. `dict.get("key").unwrap()` returns the value without "method not found" error
3. `dict.get("missing")` still returns `nil`
4. All existing tests continue to pass
5. New regression tests cover edge cases for both bugs

## Dependencies

- `src/compiler_rust/` — Rust interpreter source
- Bug reports: `doc/bug/bug_report_chained_method_unwrap_enum.md`, `doc/bug/bug_report_dict_get_auto_unwrap.md`
