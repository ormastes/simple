# rt_hal fn-typed-field invocation unresolved; SdnValue matrix residue; cli shard crash (2026-10-12)

Matrix on release_phase3 @40b5bfee423 (2026-10-12 ~04:00): test_runner_build 57
errors, compiler_cli_build HIR-shard crash. Analysis against CURRENT
origin/release/1.0 (5dc3f5a489d at investigation time).

## Class 1 (48 errors, PERSISTS): fn-typed struct field invoked as method

`unresolved method call: spawn_replay_fn / spawn_query_fn / join_until_fn /
cancel_fn / execute_pure_effect_fn / spawn_compare_fn / join_exact_until_fn /
current_owner_fn / close_fn / execute_fn / platform_available_fn` at
`src/lib/nogc_sync_mut/rt_hal/parallel_executor.spl` (18),
`rt_hal/exact_boundary.spl` (12), `rt_hal/process_task_arena.spl` (9),
`src/app/io/env_access_host.spl` (9). The rt_hal files are UNCHANGED between
40b5bfee423, current release_phase3, and current release/1.0 — not fixed
downstream.

Shape: `arena.spawn_replay_fn(...)` where `arena: RtHalTaskArenaPort` is a
plain annotated struct PARAM and `spawn_replay_fn` is a FUNCTION-TYPED FIELD
(`fn(i64, RtHalEncodedRequest) -> i64`). The Unresolved-arm field-callee
fallback (method_calls_literals.spl ~4061: `struct_field_order.has(owner) and
fields.contains(method)` -> re-dispatch as a call of the field value) should
handle exactly this (`h.f(4)` shape) but does not fire.

Evidence (SIMPLE_MIRB_TRACE=1, strict single-module compile of
parallel_executor.spl — the repro, ~70s, 6 errors):
`resolution-arm=unresolved` -> `unresolved-receiver local=31` ->
`unresolved-owner-get` -> `unresolved-owner-done` -> loud failure. Between
owner-get and owner-done the receiver's `struct_value_syms` entry is looked
up and found EMPTY: neither the direct-bind branch nor the Bug #167
value-copy branch of function_lowering.spl's param setup leaves a name on
the receiver local the method call actually sees. Both branches DO write
`struct_value_syms[local.id]` (lines 615/617, and copy_struct_value_recursive
line 556 for the copy), so the loss is either `is_named_struct` being false
at param setup (`struct_field_order.has("RtHalTaskArenaPort")` unexpectedly
empty at that point) or a rebind to a different local id later in the body.
NOT fully localized — needs an instrumentation lane (temporary eprint at the
param-setup branches + the 3490 owner lookup) with the strict compiler.

Repro: from any worktree at current sources, with the admitted stage-2:
`SIMPLE_BOOTSTRAP=1 <st2> compile src/lib/nogc_sync_mut/rt_hal/parallel_executor.spl --format=smf -o /tmp/x.smf`
(also reproduces via native-build --emit-object per the matrix.)

## Class 2 (12 errors): SdnValue payload mismatch — ALREADY FIXED, stale compiler

The 6x Dict + 6x Array 'payload type mismatch at 0' in this matrix run come
from modules whose constructions my #3156 alias-aware fallback covers
(verified by in-process MIR probe on current sources: snb_sdn's literal-path
constructions lower with ZERO mismatches; plan_sdn's var-path was probe-
verified when #3156 landed). The r3 lane's ADMITTED stage-2 predates
#3156/#3158 (both ARE ancestors of the matrix's source commit 40b5bfee423,
but the compiler binary was admitted earlier). Expected to clear on the next
admission without further source changes. If a post-#3158 matrix still shows
them, re-probe with the enum-payload eprint technique.

## Class 3: compiler_cli_build HIR-shard crash (04:00:49)

Crash report `compiler.snapshot-2026-10-12-040049.ips`: SIGABRT via rt_panic
in `cranelift_codegen_adapter.cl_translate_instruction` — the SAME stack as
the 2026-10-11 hmac crashes (phase2_cli doc family: unlowered-MIR-instruction
assert). The shard ledger names no module (claimed=0, exit=-2 at startup);
the panic message went to the swallowed stderr. This is the cranelift
backend-surface family, NOT the llvm one; the poisoned module is unextracted
from available logs. Suspect: another module-static or unlowered-instruction
shape in the full-cli closure — needs the per-module module_compile_object
diagnostics sweep or a stderr-capturing lane.
