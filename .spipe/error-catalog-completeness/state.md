# Error Catalog Completeness

**Type:** code-quality
**Status:** done
**Phase:** 8 (ship)

## Goal
Fix dangling error code references and wire catalog codes into uncataloged
error factory functions in `error.spl`, broadening semantic type error coverage
beyond literals. Scope: `error_codes.spl` + `error.spl` only.

## Acceptance Criteria

1. **AC-1:** Fix 3 dangling `with_code()` references in `error.spl`:
   `CONTRACT_PRECONDITION_FAILED` -> `PRECONDITION_VIOLATION`,
   `DIVIDE_BY_ZERO` -> `DIVISION_BY_ZERO`,
   `NULL_DEREFERENCE` -> `NULL_POINTER`.
2. **AC-2:** All ~20 `CompileError.semantic(msg)` calls in `error_factory`
   (lines 283-375) are converted to `semantic_with_context(msg, ctx)` with
   the appropriate catalog error code.
3. **AC-3:** Add new error codes for uncovered categories: `PANIC_INVOKED`,
   `CONST_BINDING_TYPE_MISMATCH`, `CONST_BINDING_NOT_FOUND`,
   `INVALID_UNIT_TYPE`, `LAMBDA_EXPECTED`.
4. **AC-4:** Every `with_code(X)` in `error.spl` resolves to a `val X = ...`
   in `error_codes.spl` (zero dangling references).
5. **AC-5:** No regressions -- existing cataloged errors unchanged.
6. **AC-6:** Scope limited to `error.spl` + `error_codes.spl`; linker/async/
   codegen typed-error schemes untouched.

## Files
- `src/compiler/00.common/error_codes.spl` -- error code registry
- `src/compiler/00.common/error.spl` -- error types + factory functions
