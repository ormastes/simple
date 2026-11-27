# Mono cannot infer a generic return-only type parameter from the expected type (E-MONO-032)

- id: mono_generic_return_ctx_inference_2026-10-27
- severity: P1 (blocked phase-3 run 6 at monomorphize, 13 failures)
- found: phase-3 run 6, stage2 `ef0681fc0e1`, windows-gnu/llvm-mingw

## Symptom
`fn rti_err<T>(code: text, message: text) -> Result<T, RtiError>` called as
`case X: rti_err(...)` / `return rti_err(...)` where the enclosing function's
return type fixes `T`. Mono reports
`E-MONO-032: call to generic rti_err ... has no explicit type args` and
`E-MONO-033` refuses to lower 13 call sites in
`src/compiler/20.hir/return_type_interface_v1.spl`.

## Workaround (tagged `@workaround bug=mono_generic_return_ctx_inference_2026-10-27`)
Helper made non-generic (`rti_error -> RtiError`); callers write `Err(rti_error(...))`.

## Fix
Root cause: `rewrite_expr_with_context_invocation_inner_v1` in
`src/compiler/40.mono/monomorphize_integration.spl` forwards expected-type
context only for direct `Call` expressions. Control-flow expressions (`If`,
`IfChain`, `MatchCase`, `Block`, `CfgSelect`) fall through to
`rewrite_expr`, which rewrites arm bodies with NO context, so a
return-only generic call in a match arm or if branch at tail position loses
the expected type.

Fix: Added arms to `rewrite_expr_with_context_invocation_inner_v1` that
forward `expected` into control-flow blocks via new helper methods:
`rewrite_if_with_context`, `rewrite_if_chain_with_context`,
`rewrite_match_with_context`, `rewrite_block_expr_with_context`,
`rewrite_cfg_select_with_context`, and `rewrite_block_opt_with_context`.
Each helper forwards the expected type to `rewrite_block(block, expected)`,
which already carries the context to the block's tail value via
`rewrite_expr_with_context`.

Red list before fix:
- match arm in tail position: E-MONO-032
- if/else in tail position: E-MONO-032
- if/elif/else chain: E-MONO-032
- nested block in match arm: E-MONO-032
- nominal type in return position: E-MONO-032

Green after fix: all 7 new spec examples pass. Regression specs all pass:
- mono_pattern_bound_type_arg_inference_spec: 3 passed
- mono_explicit_type_args_phase3_sites_spec: 4 passed
- mono_source_inference_fixed_point_spec: 5 passed
- visitor_fn_param_ctx_inference_spec: 7 passed
- mono_declared_global_inference_spec: 6 passed

Spec: test/01_unit/compiler/mono/mono_return_ctx_type_arg_inference_spec.spl
Bug id: mono_generic_return_ctx_inference_2026-10-27

Workaround removal (this change): `rti_err<T>` is restored and the
`@workaround` tag dropped (reverse of `bb8fbe29fa4`). Sequencing decided by
the coordinator 2026-10-27: stage2 is NOT redeployed for this fix; it arrives
through the stage3 compiler, built from source at or after `d8ead19f9ff8`
(PR #5039). This revert lands only after such a stage3 exists and is the one
used for the stage3 self-rebuild — merging it earlier re-breaks mono on the
old stage2 binary (E-MONO-032 x13 on this file).

## Bootstrap compatibility status (2026-10-30)

This status supersedes the preceding workaround-removal proposal; that text is
retained as historical sequencing context, not as the current status.

The workaround is **ACTIVE** again. The original source form was
`fn rti_err<T>(...) -> Result<T, RtiError>` with direct `rti_err(...)` calls,
which rely on expected-return inference. The bootstrap-compatible form is a
non-generic `rti_error(...) -> RtiError` helper with each failing caller
written as `Err(rti_error(...))`; this preserves each error code/message and
the surrounding control flow.

The earlier workaround was introduced by `bb8fbe29fa4`. It is restored here
because the actual Phase1 producer was built from
`b60d965abacfa8d21056b9344409aa2db61914ef` (SHA256
`e05b9162248105144b99ae85b1a88431e0983bcf0ac0e9a63ebc1307efe0d6bb`,
run `40157771919`, job `121062728991`, artifact `12585669434`, built October
25). That producer compiled source
`2a3d3e9bb820da44c1d6c743edf1222a3eb5a714` and left 35 generic calls
unresolved. Expected-return inference fix `d8ead19f9ff8` from October 27 is
not an ancestor of that producer. The root source fix is present in the current
source line at `902437eff3b8`, but producer compatibility has failed. Current
RTI code is therefore back on the documented workaround form; the original
generic source form must not be inferred safe from the source fix alone.

The exact-error RTI API cases have been authored but are **UNRUN**. Database
reconciliation is pending because no qualified CLI is available. No compiler,
test or native-build result is claimed here.

Remove the workaround only after all of these gates pass:

1. An admitted exact producer includes the expected-return inference feature
   from `d8ead19f9ff8` or a reviewed equivalent backport; source ancestry alone
   is not sufficient.
2. The original-form generic return-context regression runs on that exact
   producer and passes.
3. Isolated RTI compilation using the original generic helper and direct
   `rti_err(...)` callers passes on that producer.
4. The normal required verification for the resulting change passes.

A stage label, source branch update, or historical PASS does not satisfy these
gates. Cross-source producers remain acceptable when the required feature and
ABI compatibility are proven; source equality is not a global admission rule.
