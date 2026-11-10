# `bin/simple lint` aborts (SIGABRT) in cranelift `finalize_definitions` on `src/app/sj/*.spl`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-09-05
- Status: FIXED (2026-11-11, lane ne14) — lint default lane interpreter-pinned (b41d64cad69d); verified on release/1.0.0 tip, see addendum
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


## Addendum 2026-11-11 (lane ne14) — FIXED, verified on release/1.0.0

**Fixing change:** `b41d64cad69d` (2026-10-10) — lint's default lane is now the
interpreter (`interpreter_preference_reason` returns `lint-jit-parity-unproven`
for `src/app/cli/lint_entry.spl`), so the cranelift `finalize_definitions`
abort path is no longer reachable by the documented `bin/simple lint <file>`
invocation; plus the seed itself is ~2 months newer than the reported binary
(2026-09-04 aarch64 Rust seed) with extensive codegen fixes. This record's own
"Not yet established" question — "whether a pure-Simple (non-seed) bin/simple
reproduces it" — is moot for the user-facing tool: the linter no longer enters
the JIT lane by default anywhere.

**Verification actually run** (seed-smoke, worktree simple-p3-ne14-20261111,
fresh seed 46fe8f6b6def, SIMPLE_LIB=src):

| probe | 2026-09-05 verdict | today |
|---|---|---|
| `bin/simple lint src/app/sj/main.spl` | exit 134 SIGABRT in `finalize_definitions` | **rc 0**, lints to completion (0 errors, 2 warnings — real findings) |
| `bin/simple lint src/app/sj/integrate_plan.spl` | exit 134 SIGABRT | **rc 0**, lints to completion (3 errors, 5 warnings — real findings) |
| control: `bin/simple lint src/app/sj/client.spl` | exit 0 clean | exit 0 clean (unchanged) |

No `[INFO] JIT compilation failed, falling back to interpreter` and no panic
string on either offender — the runs are the pinned interpreter lane, which is
the landed mitigation. `integrate_plan.spl`'s 3 lint errors are ordinary rule
findings for that file's authors, not this defect. The `.claude/rules/
commands.md` `bin/simple lint <changed files>` step is again satisfiable for
both files.
