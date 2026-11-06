# MIR: dead tail merge block returns the i64 placeholder from a `-> f64` function (2026-11-06)

**Status:** fix-implemented-verification-pending (closes when a Stage 2 `compiler_cli_build` row passes)

## Symptom
Run-11 Stage 2 `compiler_cli_build`, `native-build src/app/office/sheets/chart.spl`:

    Failed to compile function: app.office.sheets.chart._cell_number
    - inst50 (return v39): result 0 has type i64, must match function signature of f64

## Root cause
`_cell_number` ends in a `match` whose every arm `return`s. The enum-match lowering
(`_MirLoweringExpr/switch_operators_calls.spl` ~5430, `if not result_defined:
emit_const(result, Int(0), i64)`) leaves the builder on the `ematch_merge` block with an i64
placeholder result; `_MirLowering/function_lowering.spl` (tail return, ~1092) saw no explicit
terminator and emitted `Ret(placeholder)`. No edge reaches that block, but the verifier
checks every block. Same shape for a tail `if/else` whose arms both return (spec case).

## Fix
`MirBuilder.current_block_is_dead()` (`mir_data.spl`) scans every terminator successor
(Goto/If/Switch/CallTerminator normal+unwind). The function tail keeps `Unreachable` on a
dead non-entry block instead of emitting a typed return.

## Evidence
Spec `float_text_option_lowering_spec.spl` cases "tail match" / "tail if/else": red
(1 mistyped Ret each) -> green. chart.spl native-build on run-11 Stage 2 (7daae128…):
exit 1 with the verifier error above. See green below.

Fixed Stage 2 built from commit 46f26dec9d6 (sha256 773a9ee4f2f6af44…, seed native-build of bootstrap_main.spl): chart.spl compiles with 0 AOT errors (link stops only on `__simple_main`, chart.spl has no main); p1 prints `2.5`; p3 prints `2.25`; pb prints `2.5`.
Review follow-up a9b2178923b (nil-compare fold keyed on ExistsCheck provenance), Stage 2 8fd94bdcb4c53977…: chart.spl, p1 `2.5`, p3 `2.25`, pb `2.5`, p4 nil-returning `f64?` prints `f64 none` (run-11 printed `f64 present 3.0`); parser_cli.spl and simple_ring.spl show the same output as run-11 (no new MIR/verifier/ABI errors). Spec 10/10.
