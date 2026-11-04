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
