# rt_hal fn-typed-field invocation unresolved; SdnValue matrix residue; cli shard crash (2026-10-12)

Matrix on release_phase3 @40b5bfee423 (2026-10-12 ~04:00): test_runner_build 57
errors, compiler_cli_build HIR-shard crash. Analysis against CURRENT
origin/release/1.0.

## UPDATE (instrumentation lane built, 2026-10-12): fn-field family is a stale-admitted-binary artifact

The instrumentation lane was built instead of deferred: temporary eprints at
function_lowering.spl's param-setup branches and at the Unresolved-arm owner
lookup in method_calls_literals.spl, driven by an in-process probe
(parse->HIR->MIR under the seed, 2-module closure) over
`lib.nogc_sync_mut.rt_hal.parallel_executor` — the exact failing module.

Result (current sources, full in-process lane):

- `[param-setup] fn=rt_hal_execute_parallel_safe param=arena local=4
  named_struct=true type_name=RtHalTaskArenaPort` — the param setup writes
  `struct_value_syms[4] = "RtHalTaskArenaPort"` exactly as designed (the
  elif/value-copy branch; the copy helper re-registers the copy local too).
- The fn-field probe at the Unresolved arm NEVER FIRED — no `_fn` call
  reached the Unresolved arm at all.
- **MIR ERROR COUNT: 0** — `arena.spawn_replay_fn(...)` and siblings lower
  correctly on current sources.

The matrix's admitted stage-2 (release-phase3 stage3, mtime 2026-10-12 03:40)
predates current release/1.0, on which the construct lowers cleanly. The
family is therefore expected to clear on the next admission, same class as
the SdnValue residue below. If a post-admission matrix still shows these
errors, the loss is strict/flat-LANE-specific (the full lane keeps the
registry entry; the strict lane evidently drops it) and the next
instrumentation step is the same eprint pair compiled INTO a fresh stage-2
so it fires on the native lane.

Original single-module repro (fails on the old admitted binary, expected
stale): `SIMPLE_BOOTSTRAP=1 <st2> compile
src/lib/nogc_sync_mut/rt_hal/parallel_executor.spl --format=smf -o /tmp/x.smf`.

## Class 2 (12 errors): SdnValue payload mismatch — stale admitted compiler

#3156/#3158 are ancestors of the matrix's source commit, but the admitted
stage-2 predates them. In-process MIR probe on current sources (snb_sdn
literal path): ZERO mismatches. Clears on fresh admission.

## Class 3: compiler_cli_build HIR-shard crash (04:00:49)

Crash report `compiler.snapshot-2026-10-12-040049.ips`: SIGABRT via rt_panic
in `cranelift_codegen_adapter.cl_translate_instruction` — identical stack to
the 2026-10-11 hmac crashes (unlowered-MIR-instruction assert family,
cranelift backend surface — not the llvm one). No module named (shard died at
startup, stderr swallowed). Needs the per-module `--emit-object` diagnostics
sweep or a stderr-capturing lane.
