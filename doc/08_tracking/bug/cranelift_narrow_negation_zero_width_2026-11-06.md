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
- red, run-11 Stage 2: `isub.i32`/`isub.i16 0, v ... arg 1 has type i64`, exit 1.
- green, Stage 2 rebuilt by the seed from this change (sha256 `a76e87bb...`): builds and prints
  `-1 1 -1 -2147483648 7 -128 -32768 -300`, all as expected.
- same rebuilt Stage 2: entries `data_ops.spl` and `query.spl` pass codegen (stop only at the link, no `main`).

Same defect class as draft PR #7256 (`cranelift_signed_negation_uniform_i64_2026-11-06`, another
session, not landed); this change is self-contained and does not depend on it.

## Related open bug (review finding)

`cranelift_signed_narrow_binop_no_wrap_2026-11-06` (P3, open): the BinOp call site canonicalizes
only unsigned narrow results, so a signed i32 `add`/`sub`/`mul` overflow is not sign-wrapped.
After this fix `-x` wraps at the declared width while `0 - x` does not. Not a bootstrap blocker.

## Signed BinOp candidate (2026-11-07)

`cranelift_signed_narrow_binop_no_wrap_2026-11-06` now has a source candidate;
native qualification remains pending. The ordinary `BinOp` arm previously
applied only `cl_canonicalize_unsigned_narrow` after its I64 arithmetic. Signed
I8/I16/I32 results therefore retained overflow bits, exposed by widening casts
that are no-ops in this backend.

The candidate extracts the existing signed unary-negation normalization into
`cl_canonicalize_signed_narrow` and also applies it to ordinary BinOp results:
reduce to the declared width, then sign-extend to I64. Unsigned normalization
is unchanged. Exact signed narrow destination matching leaves float, pointer,
Bool and 64-bit destinations unchanged. `CheckedBinOp` is separate and unchanged;
this candidate does not claim checked-overflow support.

New fixture `test/fixtures/compiler/cranelift_narrow_binop/wrap_signed.spl`
contains 15 authored checks: add/sub/mul overflow for all three signed widths,
minimum negation via subtraction, nonoverflow negative arithmetic, unsigned
wrap/sign distinction, floating arithmetic and a wide-integer control.
Each arithmetic helper widens the expression directly with `.to_i64()`.
An annotated narrow `let` is deliberately absent: `mir_lowering_stmts.spl`
emits an additional narrowing cast for that form, potentially masking the
missing BinOp normalization. The existing CRC32 unsigned-width regression
likewise observes arithmetic results through widening, not a narrowing let.
No compiler build or runtime test was run for this candidate.

Required qualification: a self-hosted producer containing the candidate must
native-build the fixture with `--backend=cranelift`, execute the emitted binary,
and observe exit 0 plus `PASS signed narrow binop checks=15`. Replay the existing
`cranelift_narrow_negation/negate_narrow.spl` fixture because unary normalization
now shares the helper. Preserve producer identity, compile log and executable
output. Source inspection and whitespace checks alone are not a runtime PASS.
