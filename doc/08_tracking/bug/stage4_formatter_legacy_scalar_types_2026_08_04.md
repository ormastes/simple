# Stage 4 formatter legacy scalar types

## Status

Open; retained after the third and final bounded x86 Phase 4 cycle on
2026-08-04.

## Symptom

The full CLI crossed the db-atomic, compile-target, and EasyFix type repairs.
HIR lowering then stopped in `src/compiler/tools/formatter/main.spl` on legacy
`Int` and `Bool` type annotations.

## Evidence

- Log: `build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/stage4-native-build-easy-fix-types-cycle3.log`
- Elapsed: 3m07.03s
- Peak RSS: 1,374,672 KiB
- Stub fallback: disabled
- LLVM provider: repository-managed 23.1.0-rc2 prefix

## Next action

In a fresh bounded session, inventory the formatter's exact legacy scalar
declarations, replace only semantic integer/boolean aliases with canonical
`i64`/`bool`, add a focused formatter construction/formatting native contract,
then start a new maximum-three-cycle Phase 4 sequence. Do not widen HIR type
resolution or start a fourth retry in the exhausted session.
