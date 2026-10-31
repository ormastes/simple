# HIR: `match self:` inside a generic enum's own method is rejected (2026-10-23)

**Status:** open

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

## Additional worked-around site (2026-10-31)

`src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl` (two `match
subscription.poll()` sites in the phase-1 full-CLI closure) hit the same limitation
with a non-self subject: an unqualified `TaskPollResult`-family arm match over a
method-call subject whose type is unresolved at pattern lowering. Fix, landed as
PR #5635: bind the poll result to an explicitly typed local
(`val polled: TaskPollResult<Result<i64, AsyncRefError>>`) before matching, tagged
`@workaround bug=hir_generic_enum_self_match_2026-10-23`. Verified: the module's HIR
lowers clean under the pinned stage2 (sha 6c5c53aa); the full-CLI build gate then
proceeds (a separate ctor-mir-20261031 MIR failure inside simple_ring.spl is tracked
in its own record and is the next gate).
