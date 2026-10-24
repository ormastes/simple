# HIR: `match self:` inside a generic enum's own method is rejected (2026-10-23)

Symptom: Stage 2 full-CLI build fails on `src/lib/nogc_async_mut/failsafe/core.spl`:
`generic enum pattern requires concrete declaration-ordered type arguments`, then
`E-HIR-MATCH-UNHANDLED-PATTERN: error-recovery pattern reached match lowering`.

Repro: `build/repro/generic_self_match.spl` (enum `Box2<T>` with `match self:` arms
`Ok(_)/Err(_)/Ok(v)`), `stage2ref native-build` -> hir-fatal with the two errors above
(also reproduces with `compile` of the original failsafe/core.spl).

Root cause: `lower_declared_enum_pattern`
(`src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl`, generic branch)
requires subject args to be concrete and arity-matched. The receiver type of an enum's own
method is `Named(enum, [])` / own rigid type params, so arity or concreteness fails.
Qualified `case Box2.Ok(..)` fails identically; `if self is Ok(v)` fails with unresolved `v`.

Fix (unexecuted, stage2ref is prebuilt): inside a method of the same enum, with empty or
own-type-param subject args, use the declaration's slot types as-is (identity substitution)
and skip the concreteness check. Regression spec:
`test/01_unit/compiler/20.hir/generic_enum_self_match_spec.spl` (unexecuted).

Workaround (verified: stage2ref HIR of failsafe/core.spl has 0 hir-fatal; original has 1):
`val subject: FailSafeResult<T> = self` then `match subject:` in `is_ok/unwrap/unwrap_or`,
tagged `@workaround bug=hir_generic_enum_self_match_2026-10-23`. Keep bug open; retire the
workaround after the fix is deployed in a Stage 2 producer.

Same shape elsewhere: `src/lib/nogc_sync_mut/failsafe/core.spl` (FailSafeResult<T>, 3 methods) -
unchanged. DB reconciliation pending.
