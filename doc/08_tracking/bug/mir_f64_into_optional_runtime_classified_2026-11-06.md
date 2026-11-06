# MIR: f64 value wrapped into `f64?` is classified at runtime via rt_enum_id(i64) (2026-11-06)

**Status:** fix-implemented-verification-pending (closes when a Stage 2 `compiler_cli_build` row passes)

## Symptom
Run-11 Stage 2 `compiler_cli_build` (full main_and_help closure):

    [cranelift] E-BACKEND-CRANELIFT-CALL-ABI: call to rt_enum_id ... app.office.sheets.spreadsheet._parse_f64:
      arg 0 is f64 but the callee declares i64

for `fn _parse_f64(s: text) -> f64?: return office_parse_signed_decimal_f64(s)`
(spreadsheet.spl:308; callee returns plain f64, src/lib/common/office/number.spl:33).

## Root cause
`ensure_option_handle` (`_MirLoweringExpr/switch_operators_calls.spl`) wraps statically only
when `local_is_provably_scalar_payload` holds. That predicate returned false for any local in
`extern_result_locals` / runtime-value sets BEFORE consulting the MIR slot type, so an F64
local went to `normalize_option_handle`, which calls `rt_enum_id(i64)` on it. A float slot
can hold neither an Option handle nor the nil word.

Standalone repro (`build/probe/pb.spl`): `extern fn rt_math_sqrt(x: f64) -> f64` returned
from `fn root_opt(x: f64) -> f64?` gives the identical CALL-ABI error on run-11.

Full-closure mechanism (inferred from code, not traced): the driver reuses ONE `MirLowering`
for every module (`80.driver/driver_pipeline_lowering.spl:1173`), and `extern_fn_symbols`
is only initialised at construction (`_MirLowering/module_lowering.spl:580`), keyed by
symbol id. An extern declared in an earlier module whose symbol id equals the id of
`office_parse_signed_decimal_f64` in spreadsheet's table marks the call result as an extern
result. That stale-key collision is a separate latent defect (not changed here).

## Fix
`local_is_provably_scalar_payload` returns true for an F32/F64 MIR slot first;
`normalize_option_handle` fails closed (error) on a float local instead of emitting a
mistyped call.

## Evidence
Spec case "extern f64 into f64?": red (rt_enum_id present) -> green (rt_enum_new only).
pb.spl on run-11 Stage 2 (7daae128…): CALL-ABI exit 1; see green below.

Fixed Stage 2 built from commit 46f26dec9d6 (sha256 773a9ee4f2f6af44…, seed native-build of bootstrap_main.spl): chart.spl compiles with 0 AOT errors (link stops only on `__simple_main`, chart.spl has no main); p1 prints `2.5`; p3 prints `2.25`; pb prints `2.5`.
