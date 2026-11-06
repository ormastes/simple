# Cranelift: unary minus on i8/i16/i32 emits a narrow zero against an I64 lane value (2026-11-06)

**Status:** fix-implemented-verification-pending (closes when a Stage 2 `compiler_cli_build` row passes)

Run 11 (base `e4c8830efc7`, Stage 2 sha256 `7daae128...`) row `compiler_cli_build` failed codegen in
`app.office.sheets.data_ops._compare_row_cells` and `app.office.sheets.query._row_key_compare`:

    inst454 (v351 = isub.i32 v350, v349  ; v350 = 0): arg 1 (v349) has type i64, expected i32

Both negate an `i32` comparison result (`-cmp`).

## Cause

`cl_translate_unaryop` (`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`, `Neg`
integer arm) created the zero with `mir_type_to_cl(operand_type)` (I32 for an `i32` operand),
while this backend keeps every integer SSA value as I64. `isub.i32 0, <i64>` fails the verifier.

## Fix

The zero is I64. For a signed narrow operand (I8/I16/I32) the I64 difference is reduced to the
declared width and sign-extended back, so negating the minimum wraps at that width
(`-(-2^31) == -2^31`). Unsigned narrow results are still canonicalized by the existing
`cl_canonicalize_unsigned_narrow` at the call site.

## Evidence

Fixture `test/fixtures/compiler/cranelift_narrow_negation/negate_narrow.spl`, phase-C argv
(`native-build <entry> --backend=cranelift --low-memory`, `SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP=1`, 16G cgroup):
- red, run-11 Stage 2: `isub.i32 v4, v3 ... arg 1 (v3) has type i64, expected i32`, exit 1.
- green, Stage 2 rebuilt by the seed from this change (sha256 `1754656a...`): builds and prints
  `-1 1 -1 -2147483648 7`, all as expected.
- same rebuilt Stage 2: entries `data_ops.spl` and `query.spl` pass codegen (stop only at the link, no `main`).

Same defect class as draft PR #7256 (`cranelift_signed_negation_uniform_i64_2026-11-06`, another
session, not landed); this change is self-contained and does not depend on it.
