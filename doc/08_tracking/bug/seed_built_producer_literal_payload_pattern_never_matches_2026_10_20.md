# Seed-built producer: `case HirTypeKind.Int(64, true):` never matches

- Canonical id: seed_built_producer_literal_payload_pattern_never_matches_2026_10_20
- Date: 2026-10-20
- Status: open; worked around in `src/compiler/50.mir/_MirLoweringExpr/result_tuple_payload.spl`
  (PR #3914) by using binding patterns.
- Evidence: a producer built from work/p6-mir-misc by the Rust seed (cranelift, strict link,
  `C:/dev/simple-bootstrap-storage/fixer-p6misc/producer/simple-producer-misc-strict.exe`)
  rejected `Result<(text, i64), text>` with the new diagnostic
  "unsupported Result tuple payload element type: slot 1 is Int(64, true)" — i.e. the HIR kind
  was `Int(64, true)`, yet `case HirTypeKind.Int(64, true): Some(MirType.i64())` in
  `result_try_tuple_field_type` did not match. This is also why phase 3 rejected plain
  `Result<(i64, i64), text>` (`_SmfReaderMemory/header_parser.spl:241`). After rewriting the arm
  as `case HirTypeKind.Int(bits, signed): if bits == 64 and signed: ...` the same fixture
  builds and runs correctly.
- Not reproduced in user code: the same literal-payload match on a user enum
  (`case Int(64, true):`) built by producer6 / the rebuilt producer with the llvm backend
  matches correctly, so the defect is in how the seed compiles the compiler (most likely the
  `bool` literal sub-pattern against a HirTypeKind payload), not in the language.
- Other literal-payload arms in compiler source that may be dead under a seed-built producer:
  `20.hir/hir_verification.spl:8-12`, `50.mir/_MirLowering/function_lowering.spl:929`,
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl:6425`,
  `60.mir_opt/_OptimizationPasses/engine.spl:757,764`, `70.backend/codegen_enhanced.spl:325`.
