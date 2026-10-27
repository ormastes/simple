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

The tagged workaround in src/compiler/20.hir/return_type_interface_v1.spl
remains in place pending a stage2 binary carrying this fix (a source fix
alone does not unblock stage2 builds until the stage2 binary is redeployed).
