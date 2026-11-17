# MIR named default rejects empty array literal (2026-11-17)

Status: verification-pending

Phase-3 native-build (stage2, in-process MIR, no declaration repository) failed:
`MIR lowering error: named default requires admitted declaration scope: compiler.frontend.parser_types.parser_module_new.friends`.

Cause: `named_call_slots_v1` (src/compiler/50.mir/_MirLowering/named_call_arguments_v1.spl) in the
`bootstrap_fn_param_defaults_lookup` branch only admitted scalar/string literal defaults; `friends: [text] = []`
is an empty `ArrayLit`.

Fix: admit `HirExprKind.ArrayLit(elements, _)` when `elements.len() == 0` (no captures, fresh per call; lowered by
`complete_named_call_operands_v1` through the generic default path). Non-empty arrays and dict literals stay rejected.

Repro/prevention: test/01_unit/compiler/mir/named_default_empty_array_spec.spl (accept empty, reject non-empty).
