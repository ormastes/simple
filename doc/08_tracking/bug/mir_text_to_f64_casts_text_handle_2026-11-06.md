# MIR: `text.to_f64()` casts the text handle to f64 instead of parsing (2026-11-06)

**Status:** fix-implemented-verification-pending (closes when a Stage 2 `compiler_cli_build` row passes)

## Symptom
`"2.5".to_f64()` compiled by the run-11 Stage 2 compiler printed `207130714919617.0`
(silent wrong value). Same lowering produced the `Cast(text -> F64)` in
`app.office.sheets.chart._cell_number` (src/app/office/sheets/chart.spl:31).

## Root cause
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`: the primitive text builtin
arm (`primitive_text_method_shape` ~2625, dispatch ~4063, `ts_sym` match) listed `to_float`
but not `to_f64`/`to_f32`, although the interpreter treats all three as one total parse
(`interpreter_method/string.rs:451`). A proven text receiver therefore fell to the
Unresolved numeric conversion arm (~5190), which emits `MirInstKind.Cast(receiver, F64)` —
a numeric conversion of the text handle word.

## Fix
- `to_f64`/`to_f32` join the text arm for PROVEN text receivers only (erased receivers stay
  with the numeric arm), lowering to `rt_string_to_float` + `rt_value_as_float` (+ `Cast F32`
  for `to_f32`).
- The numeric float conversion arm now fails closed on a text receiver instead of casting.

## Evidence
Spec `test/01_unit/compiler/50.mir/float_text_option_lowering_spec.spl` (seed interpreter,
MIR shape): red 1/6 -> green 6/6. Native probe `build/probe/p1.spl` on run-11 Stage 2
(sha256 7daae128…): `207130714919617.0`; see green below.

Fixed Stage 2 built from commit 46f26dec9d6 (sha256 773a9ee4f2f6af44…, seed native-build of bootstrap_main.spl): chart.spl compiles with 0 AOT errors (link stops only on `__simple_main`, chart.spl has no main); p1 prints `2.5`; p3 prints `2.25`; pb prints `2.5`.
Review follow-up a9b2178923b (nil-compare fold keyed on ExistsCheck provenance), Stage 2 8fd94bdcb4c53977…: chart.spl, p1 `2.5`, p3 `2.25`, pb `2.5`, p4 nil-returning `f64?` prints `f64 none` (run-11 printed `f64 present 3.0`); parser_cli.spl and simple_ring.spl show the same output as run-11 (no new MIR/verifier/ABI errors). Spec 10/10.
