# `bin/simple lint` aborts (SIGABRT) in cranelift `finalize_definitions` on `src/app/sj/*.spl`

- Date: 2026-09-05
- Status: OPEN
- Severity: tooling — the linter cannot be run at all on two files on the landing path
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, 154560904 bytes, mtime 2026-09-04 14:46:17 +0900 (Rust seed)

## Symptom

```
bin/simple lint src/app/sj/main.spl          # exit 134, core dumped
bin/simple lint src/app/sj/integrate_plan.spl # exit 134, core dumped
```

Backtrace tail (identical for both):

```
 7: core::panicking::panic
 8: <cranelift_jit::backend::JITModule>::finalize_definitions
 9: <simple_compiler::codegen::jit::JitCompiler>::compile_module
10: <simple_compiler::codegen::local_execution::LocalExecutionManager as ...ExecutionManager>::compile_module
11: <simple_driver::exec_core::ExecCore>::run_file_jit
```

This is the lint tool's own JIT aborting, not a lint finding. No verdict line is
emitted, so the run is indistinguishable from a crash of the linted program if
the exit code is not read.

## Pre-existing, not caused by in-flight work

Verified by controls on the same binary in the same working tree:

- `bin/simple lint src/app/sj/client.spl` (untouched sibling) — exit 0,
  `Lint passed: all files clean`. So lint is not globally broken.
- The **unmodified `HEAD` content** of both offenders was checked out over the
  working copy and linted: `git show HEAD:src/app/sj/main.spl` — exit 134;
  `git show HEAD:src/app/sj/integrate_plan.spl` — exit 134. Both then restored.

So the abort reproduces on committed content and is not introduced by the
2026-09-05 legacy-argv dry-run wiring.

## Impact

`.claude/rules/commands.md` prescribes `bin/simple lint <changed .spl files>` for
changed files. That step cannot be satisfied for any change to
`src/app/sj/main.spl` or `src/app/sj/integrate_plan.spl` until this is fixed;
those changes ship lint-unverified. `bin/sj` itself is unaffected — `bin/sj
--help`, `bin/sj status` and `bin/sj plan ...` all run normally, so only the lint
path JITs whatever it is that panics.

## It is not the lifecycle import graph

`src/app/sj/plan_main.spl` (added the same day) imports
`app.sj.integrate_plan` — and therefore `app.sj.lifecycle_policy` and
`std.scv.lifecycle.model` — and lints **clean**, exit 0, `Lint passed: all files
clean`. `src/app/sj/main.spl` still aborts after its `app.sj.integrate_plan`
import was removed again (exit 134). So the trigger is something in the two
offending files themselves, not the modules they pull in.

## Not yet established

- Which declaration in those two files triggers it (no bisection was run).
- Whether the panic is a cranelift assertion on a duplicate/unfinalized symbol
  definition, which would connect it to the pre-existing
  `compiler_cross_module_private_symbol_collision` warnings this binary already
  emits for `env_get`, `file_read_text_at`, `process_run_with_limits` and
  `process_wait` on every `sj` invocation.
- Whether a pure-Simple (non-seed) `bin/simple` reproduces it.

Crash reports were written to `.simple/logs/crash_2055979.log`,
`.simple/logs/crash_2056619.log`, `.simple/logs/crash_2056845.log`,
`.simple/logs/crash_2057276.log`.
