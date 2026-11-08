# Callback field dispatch and indirect return owner loss

Status: fix-implemented-verification-pending (2026-11-08). Canonical bug ID: `runner_callback_field_owner_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/2980

## Root cause and fix (2026-11-08)

`lower_call_with_value` (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`)
already recovered the declared `fn(..) -> Record` signature of a callback
field through `receiver_declared_type` -> `declared_field_hir_type` for an
explicit call `(port.execute_fn)(x)`, but used it only to type the arguments
and set an `indirect_return` value that `emit_typed_function_value_call`
never reads. The signature actually used for emission came from the
projected callee local's HIR type (absent or an erased scalar for
entry-closure / loop-binding shapes) or from `enum_match_expr_type`, which
has no `Field` arm. The call therefore failed closed with
`indirect callable lacks a proven function signature`, or ran the legacy
word-ABI path with no return owner so `observed.status` on the aggregate
result was unresolved -- the "unresolved callback fields" MIR errors in
`env_access_host` / `rt_hal_isolated_host`.

Fix: retain the declared callable type and use it as the indirect call's
signature whenever the callee local does not itself prove a callable
(`Function` / `Optional<Function>`) type. A callee local that proves its own
callable type is never overridden.

- Reproducing spec: `test/01_unit/compiler/mir/callback_field_explicit_call_owner_spec.spl`
  (3/3; before the fix: 2 failures, `indirect callable lacks a proven function signature`).
- Generalization spec: `test/01_unit/compiler/mir/callback_field_declared_signature_generalization_spec.spl`
  (erased scalar callee type, nested `host.port.execute_fn` chain, no override of a proven callee type; 3/3, 2 failed before).
- Original-form fixture (no owner-retaining wrappers):
  `test/fixtures/compiler/callback_field_explicit_call/original_form.spl` -- interpreter PASS.
- NOT done: native qualification of the actual consumers on a rebuilt producer. The
  `@workaround` sites in `src/lib/nogc_sync_mut/rt_hal/*.spl` and the wrapped `main.spl`
  fixture stay until that runs. Pre-existing, unrelated: `indirect_call_return_owner_spec.spl`
  and `fn_typed_parameter_indirect_call_spec.spl` fail 7/8 with and without this fix
  (stale 4-argument `emit_typed_function_value_call` calls and the pre-v1 ownership-proof format).

Original failure: C35 full runner: HIR251 PASS, MIR20 errors including callback fields; initial workaround ARM exit14 exposed record field owner loss.

Workaround commits:

- `a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3`; recovery parent `ea9224a83a64cd20e21d013cf1c2652f891999c4` (review only).
- `83ec8208a4ebe8dd0330cdf72907c23528c6c803`; recovery parent `a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3` (review only).
- `1de4827be3b6e3d86c101d9d0214b850f3feb932`; recovery parent `83ec8208a4ebe8dd0330cdf72907c23528c6c803` (review only).

Current qualification: C35 narrow fixture ARM runtime PASS with10effects; RISC-V ELF243 object PASS, not execution. Actual C36 env_access_host and rt_hal_isolated_host consumer MIR still FAIL on unresolved callback fields. No runner qualification.

Producer: `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c35-callback-field-workaround/{arm-final,rv-final-monitor-3002}/; /home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-consumer-fixes/`.

Reproducing/prevention source: `test/fixtures/compiler/callback_field_explicit_call/main.spl`.

Background fix owner and removal condition: Permanent method-field layout and indirect-call return provenance owner; reviewed compiler pair273368/e2b959 remains separate. Remove only after original dot-field calls and aggregate returns pass actual consumers and fixtures on admitted replacement producer.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3 -> ff6ddda35330aac9da65c717d61bf5254102577d (stable patch-id equal; both UNLANDED on checked release); 83ec8208a4ebe8dd0330cdf72907c23528c6c803 -> da6ef256e3a660a3a12861c0a3685da2e97bc4ad (stable patch-id equal; both UNLANDED on checked release); 1de4827be3b6e3d86c101d9d0214b850f3feb932 -> 0f23b123e0817c1b3a7c0694e5dc5608e3d45407 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Narrow ARM/RISC-V fixture source 1de4827be3b6e3d86c101d9d0214b850f3feb932; actual C36 consumer integrationf7fdaf remains failing.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.

Additional consumer workaround: Additional source workaround 64b8854eaa6eee9470470ddbcef5fa2165902d13 (recovery parent f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c) replaces 11 remaining actual process_task_arena callback calls and retains 7 typed host locals. Source reviewed; changed-consumer native qualification PENDING. This is UNLANDED as of release 95c12f073ffefa99ac774264beeedd68a47e7676 and does not extend prior narrow fixture PASS. Source link https://github.com/ormastes/simple/commit/64b8854eaa6eee9470470ddbcef5fa2165902d13.

**2026-11-03 (sonB): deferred.** Needs the permanent method-field layout/indirect-call return provenance owner in MIR; requires C36 consumer MIR repro on stage3; workaround kept.
