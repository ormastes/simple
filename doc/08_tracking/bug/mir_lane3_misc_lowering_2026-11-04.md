# MIR lane 3 misc lowering specs (2026-11-04)

Seed: cargo-rel100/simple-ref. Specs under test/01_unit/compiler/50.mir/.

| spec | class | root cause | fix | before -> after |
|---|---|---|---|---|
| inline_typed_bytes_load_spec | product bug | `backend/riscv_target.spl` imported `hardware.riscv_common...` (no `std.` prefix); the baremetal Riscv64 config path failed with `variable RiscvTargetAbi not found` | import via `std.hardware...` | 6/7 -> 7/7 |
| lambda_lift_remaining_kinds_capture_scan_spec | product bug | `lower_lambda_value_for_type` propagated `class_type_names` to the lifted sub-lowering only when `declaration_repository != nil`; a class constructor inside any lambda body hit "missing class provider metadata" in the full-HIR lane | propagate `class_type_names` next to `struct_field_order` unconditionally | 18/19 -> 19/19 |
| value_feature_breadth_lowering_spec | stale fixture | fixture assigned captured `acc` in a lambda (compile error by owner ruling, language.md) and called an unannotated lambda local (`indirect callable lacks a proven function signature`, fatal by design) | fixture returns the new value and annotates `fn(i64, i64) -> i64` | 8/9 -> 9/9 |
| for_in_runtime_tuple_decode_spec | stale expectation | `for (key, value) in dict` over a struct-valued dict now also emits the by-value record copy (GetField 0,1 + Aggregate Struct) | field index expectation `[0,1,0,1,1]` | 12/13 -> 13/13 |
| builtin_method_extras_guard_spec | stale (2) | `Result.ok()` over a struct payload is now supported; comprehension over `[u8]` now lowers via `rt_bytes_u8_at` (fe3967ffd43) | positive assertions; `[u64]` comprehension rejection kept as its own example | 41/43 -> 43/43 |
| function_lowering_any_early_return_todo_spec, function_lowering_stmt_probe_trace_todo_spec, ghost_erasure_dict_iteration_todo_spec | in-development | `@tag:in-development` fail-fast placeholders (TODO #433/#436/#432, coverage_wave2_found_bugs_2026-11-02.md) | none, left RED | unchanged |

Follow-ups: the dict-pair struct copy is correct value semantics (Bug #177); the
enumerate path is the one that skips the copy -- filed as
`mir_enumerate_struct_binding_skips_value_copy_2026-11-05.md`. isel_riscv64_spec
(2/42 -> 3/42) and portable_numeric_capabilities_spec (5/10 -> 6/10) remain red
for unrelated reasons.
