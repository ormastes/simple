# A main-less script that fails at runtime runs twice (2026-11-13)

- **Id:** `no_main_runtime_error_reruns_on_interpreter_2026-11-13` (P2,
  duplicate side effects).
- **Found by:** PR #8967 (`visibility_error_jit_fallback_fail_open_2026-11-13.md`),
  which closed only the visibility-error instance of this class.
- **Branch:** `work/no-main-runtime-error-rerun-20261113` on `release/1.0.0`
  (base `27e5596bd97`). **Model:** Opus (Fable unavailable).

## Symptom

```
print "A"
val xs = [1]
print xs[5]          # runtime error, no fn main
```

`simple noman.spl` on the seed's default JIT lane printed `A`, the runtime
error as an `[INFO] JIT compilation failed, falling back to interpreter` line,
then `A` again and the error a second time. Every side effect before the
failure (file writes, network calls, process spawns) happened twice.

## Root cause

For a file without `fn main`, `run_file_jit` does not JIT anything: the
`jit-bail:no-main-fn` arm runs the whole module on the tree-walk interpreter
itself (`evaluate_module(&ast.items)`) and returns its error as a plain
`String`. `run_file_with_args` could not tell that error from a genuine
"this module cannot be JIT-compiled" error, so its `Ok(Err(jit_err))` arm
treated a program that had ALREADY RUN and failed as a JIT gap and ran
`run_file_interpreted_with_args` in the same process. PR #8967 patched one
message shape (`is_private_fn_visibility_error`); every other runtime error
still re-ran.

## Fix

Structural, not message matching. `run_file_jit`'s body moved to
`run_file_jit_outcome`, which returns `JitRunError`:

- `Unsupported(String)` -- the JIT could not compile or run the program;
  nothing of the user's program ran, so the interpreter fallback is safe.
- `AlreadyExecuted(String)` -- the interpreter inside the no-main arm already
  ran the program and it failed. `run_file_with_args` propagates it with no
  rerun and no `[INFO] ... falling back` line.

The public `run_file_jit -> Result<i32, String>` is a thin wrapper. The
no-main error path now also clears the current file and collects GC, which
the `?` used to skip (masked by the rerun).

## Not changed here (same class, still open)

- `em.execute("main")` failing after JIT'd `main` started, and the
  `catch_unwind` panic arm (a panic raised while the no-main interpreter run
  was executing): both still fall back and can re-run side effects.
- The no-main arm never calls `set_interpreter_args`, so `rt_cli_get_args` /
  `rt_cli_arg_count` / `rt_cli_arg_at` (thread-local `INTERPRETER_ARGS`) read
  empty there (`sys_get_args`/`rt_get_args` are fine). Before this fix a
  runtime failure caused by that was hidden by the rerun, which had the args.
  Pre-existing; candidate fix: `set_interpreter_args(args.clone())` before the
  JIT attempt in `run_file_with_args`.
- The Rust test shares the process with
  `imported_simple_function_links_under_strict_jit`, which sets
  `SIMPLE_JIT_STRICT`; run it name-filtered or `--test-threads=1` (same
  exposure as `private_import_from_other_dir_fails_closed_on_jit_lane`).
- `run_source_in_memory_native` has the same no-main interpreter arm but its
  callers propagate with `?` and never rerun, so it is not affected.

## Evidence

- Rust: `exec_core::execution_mode_validation_tests::no_main_runtime_error_runs_once_on_jit_lane`
  (side-effect file must hold exactly one line, result must be `Err`).
- Spec: `test/01_unit/compiler/95.interp/interpreter/no_main_runtime_error_no_rerun_spec.spl`.
