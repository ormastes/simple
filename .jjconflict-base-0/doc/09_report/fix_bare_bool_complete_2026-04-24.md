# Fix Bare Bool Suppressions — Completion Report
**Date:** 2026-04-24  
**Task:** fix-bare-bool-suppressions

## Summary

Removed all unjustified `@allow(bare_bool)` and `#![allow(bare_bool)]` suppressions from the codebase by adding a predicate-function exemption to the Rust AST lint.

## Changes

### Rust AST Lint Exemption (D-1)
- Added `is_pure_predicate_function()` to `src/compiler_rust/compiler/src/lint/checker_core.rs`
- Wired into `check_function()` and `check_trait()` in `src/compiler_rust/compiler/src/lint/checker_types.rs` via narrow `check_type_in_public_api_skip_bare_bool()` helper
- Exemption criteria: function name starts with `is_/has_/can_/should_/will_/contains_/must_/needs_`, return type is `bool`, and no parameter has bare `bool` type

### Suppressions Removed
- `src/lib/` — 12 files: both `@allow(bare_bool)` and `#![allow(bare_bool)]` removed
- `src/compiler_rust/lib/std/` — 42 standalone `#![allow(bare_bool)]` files + 2 combined-form files (bare_bool stripped from primitive_api combo in fs_types.spl and transport.spl)

### Remaining Justified Suppression
- `src/compiler_rust/lib/std/src/testing/fuzz.spl` — 1 suppression with comment:
  > BoolGen.generate() -> bool (name not predicate-prefixed, cannot be renamed without breaking API) and fn(any) -> bool property parameter are stdlib primitive boundary.

### Spec Coverage
- `test/code_quality/bare_bool_lint_spec.spl` — 7/7 passing (text-scanner param behavior)
- `test/code_quality/bare_bool_types_spec.spl` — 8/8 passing (alias pattern + predicate naming)

## Verification Results

| Check | Result |
|-------|--------|
| bare_bool_lint_spec | 7/7 PASS |
| bare_bool_types_spec | 8/8 PASS |
| Unjustified suppressions remaining | 0 |
| Justified suppressions remaining | 1 (fuzz.spl) |
| Build (Rust clippy) | PASS (pre-existing warnings only, unrelated) |
| System test failures | 7 pre-existing (GUI/SSH/TLS infra, unrelated) |

## Files Modified

- `src/compiler_rust/compiler/src/lint/checker_core.rs` — added `is_pure_predicate_function()`
- `src/compiler_rust/compiler/src/lint/checker_types.rs` — wired predicate exemption
- 12 files in `src/lib/nogc_sync_mut/` — suppressions removed
- 44 files in `src/compiler_rust/lib/std/` — suppressions removed
- `test/code_quality/bare_bool_lint_spec.spl` — new (7 specs)
- `test/code_quality/bare_bool_types_spec.spl` — new (8 specs)
