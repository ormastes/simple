# Seed JIT HIR rejects a positional argument after a named one; interpreter accepts it

- **Filed:** 2026-11-04 (libbug coordinator)
- **Status:** open (compiler); call sites fixed in lib/app
- **Symptom:** `run_test_file_jit(file_path: file_path, options, arch: arch, target: target)`
  makes the seed JIT HIR report `call to run_test_file_jit passes parameter 1 more than once
  or beyond its arity` and drops the whole `src/app/test_runner_new/main.spl` module to the
  interpreter (`[jit-fallback]`). The tree-walk interpreter binds the same call correctly.
- **Divergence:** interpreter and JIT disagree on positional-after-named binding. The syntax
  guide documents only positional-then-named (`connect("localhost", port: 3000)`).
- **Decision needed:** either reject positional-after-named in the parser with a clear
  diagnostic (both engines), or bind it by position-after-named-slots in the JIT HIR.
- **Lib fix:** the four call sites in `test_executor_composite.spl` (app + nogc_sync_mut) now
  pass `options: options`; the runner module JIT-compiles again (0 HIR lowering errors).

## Fixed — 2026-11-05 (PR #6890)

Decision taken: the second option (bind in the JIT HIR). The interpreter's
binding rule — trailing positional arguments fill the lowest UNFILLED slots
in declared order — is now what `bind_named_call_args` implements (the
positional cursor skips slots a named argument already took). Divergence
reproduced on the deployed seed before the fix: `combo(1, c: 3, 2, 4)`
(lowered JIT HIR: "parameter 3 more than once or beyond its arity" +
jit-fallback) vs interpreter A=1234/B=1234. Rust regression
`positional_args_after_named_fill_lowest_unfilled_slots` pins the
declared-slot order (fails without the fix); all 61 named-argument tests in
the crate pass. Canonical positional-then-named calls are unaffected.
