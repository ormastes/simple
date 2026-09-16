# Stage 4 formatter legacy scalar types

## Status

Fixed. Exact x86 Phase 4 cycle 1 crossed the formatter with the refreshed
LLVM 23.1 Stage 3 producer.

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

## Repair and focused evidence

The formatter's 11 semantic integer annotations and six boolean annotations
now use canonical `i64` and `bool`. The reassigned `print_diff` maximum is now
mutable. Source-contract expectations were updated to match those declarations.

A temporary focused formatter contract passed HIR/code generation and emitted
objects, then the strict `core-c-bootstrap` link exited 1 on unresolved
`rt_file_atomic_write`. The diagnostic is retained in
`build/focused/stage4-formatter/native-build.log`; it is not an executable PASS
and the temporary contract was removed rather than making the minimal runtime
bundle a false formatter requirement. The provider/owner partition remains the
separate `stage4_runtime_core_owner_gap_2026-07-18.md` concern.

Cycle 1 continued to `compiler.tools.fix.main`, proving the formatter no longer
blocks HIR. Evidence:
`build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/stage4-native-build-formatter-cycle1.log`.
