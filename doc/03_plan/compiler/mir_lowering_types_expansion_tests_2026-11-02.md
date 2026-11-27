# MIR lowering-types expansion tests (deferred, TODO 431)

Non-essential; fail-fast specs only, no implementation. Target: `src/compiler/50.mir/mir_lowering_types.spl`
and `_MirLowering/function_lowering.spl` `lower_type` (coverage-wave-2 baseline: `doc/09_report/generics_coverage_baseline.md`).

| Slice | Spec | Intent |
|---|---|---|
| Table-driven | `test/01_unit/compiler/50.mir/mir_lowering_types_table_spec.spl` | one row per `HirTypeKind` variant (`src/compiler/20.hir/hir_types.spl`), exhaustiveness check |
| Property | `.../mir_lowering_types_property_spec.spl` | determinism, idempotence, no nil result |
| Depth / large struct | `.../mir_lowering_types_stress_spec.spl` | deep nesting, 10k-field struct, RSS ceiling |
| Regression | `.../mir_lowering_types_regression_spec.spl` | E-MIR-TYPE-TypeParam, E-MIR-TYPE-Transport, E-RTI-007 (`doc/08_tracking/bug/rti007_any_return_rows_2026-11-01.md`) |
| Negative controls | `.../mir_lowering_types_negative_spec.spl` | must-reject and must-not-over-reject cases |

All bodies are `fail("TODO #431: ...")`, tagged `@tag:in-development`.
