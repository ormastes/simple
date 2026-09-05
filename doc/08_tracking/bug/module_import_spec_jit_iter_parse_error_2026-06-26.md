# Bug: module_import_spec — JIT compile fails on iter.spl, 2 tests wrong

**Date:** 2026-06-26
**Spec:** test/01_unit/lib/common/module_import_spec.spl
**Status:** Source fixed; execution verification pending

## Symptom

2 of 23 tests fail:
- "parses export A, B from module"
- "parses export group from module"

Both expect a `warning: Consider explicit exports to avoid exposing internal APIs` message but instead get a JIT compilation error:
```
[INFO] JIT compilation failed, falling back to interpreter: module load error:
parse: in ".../src/compiler_rust/lib/std/src/core/iter.spl":
Unexpected token: expected Newline after impl block colon, found Identifier { name: "Iterator", pattern: TypeName }
```

## Root Cause

The seed parser rejects `impl Type: Trait` single-line header form in `iter.spl`. This parse error causes JIT to fail and fall back to interpreter, but the fall-back path emits an error message rather than the expected warning. The tests then fail because the expected warning string is not present.

## Fix Required

Either:
1. Fix the parser in the Rust seed (`src/compiler_rust/`) to accept `impl Type: Trait` header form on a single line
2. Or update `iter.spl` to use the form the parser accepts
3. Or fix the test fallback path to still emit the expected warning even when JIT fails

## Resolution (2026-07-15)

The five iterator implementations in `core/iter.spl` now use the
canonical `impl Trait for Type` grammar. The seed parser retains its strict
grammar. The existing module-import spec covers the original JIT/import path;
its execution remains pending an authorized runtime test run.
