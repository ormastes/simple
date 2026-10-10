# `simple lint` SEGV (rc=139) on every file — text passed as `[String]`, then a JIT lane that lies

Date: 2026-10-10. Branch: `release/1.0`. Host: Windows x86_64, Rust seed.

## Symptom

`simple lint <any file>` — including a two-line hello world — printed the
loader warnings, one `[engine-demotion] reason=hybrid-interp-splice` line, and
died with `0xC0000005` (rc=139 under Git Bash) and no verdict line.
`SIMPLE_EXECUTION_MODE=interpreter simple lint <file>` passed in 7-14 s on
small files (large compiler files take up to ~560 s interpreted).

## Bisect

First bad first-parent merge on `release/1.0`: `a83547311a6` (PR #2758,
2026-10-09 20:34). Its parent `4f3788f715d` still takes the interpreter
fallback (`[engine-demotion] reason=jit-compile-error`) and does not crash.

#2758 did not introduce the crash. It fixed `cl.code` -> `cl.trimmed` in
`src/compiler/35.semantics/lint/linear_scan_in_loop.spl` (`CodeLine` has no
`code` field). Until then that field made every JIT attempt on
`src/app/cli/lint_entry.spl` fail with `HIR lowering error: Cannot infer field
type: struct 'CodeLine' field 'code'`, so lint silently fell back to the
interpreter on every run. Removing the error switched the JIT lane on for the
first time, and three latent defects surfaced one after another.

## Defect 1 — the SEGV (FIXED)

`src/compiler/90.tools/lint/_LintMain/lint_checks.spl:277-281` passed
`content` (a `String`) to five checks declared `lines: [String]`
(`traceability_and_assertions.spl:180,222,426,470,521`). lldb, with
`SIMPLE_JIT_TRACE_ADDR=1` to symbolise the JIT heap:

    Access violation reading 0xffffffffffffffff
    pc = Linter.check_ui_raw_widget_kind+0x226    movq (%r9,%rcx,8), %rax

i.e. `for line in lines` indexing a string as an 8-byte-element array.

History: `6a0688ad695` (2026-08-22, "perf(lint): share lines with quality
checks") changed both the signatures and the call sites. `4edef8fab8e`
(2026-08-26, "snapshot current development state") reverted only the call
sites — a stale-snapshot rewind. On the interpreter this was silent and wrong
rather than fatal: iterating a string yields characters, so UI001/UI002/UI003,
the spipe quality check and the feature-tracking done gate could not match
anything for six weeks.

Fix: pass `lines` again at all five call sites.

## Defect 2 — JIT has no `Array.sort_by` (OPEN, seed)

With defect 1 fixed the JIT lane exits 70:
`Runtime error: Function 'Array.sort_by' not found`, from
`src/compiler/90.tools/fix/rules/impl_/lint_code.spl:156`. The interpreter
implements it (`interpreter_method/mod.rs`); the builtin-method table in
`codegen/common_backend.rs` (`rt_map`, `rt_array_filter`, ...) has no arm.

## Defect 3 — JIT reports a dirty file as clean (OPEN, seed)

With `sort_by` replaced by a plain loop (experiment only, not landed) the JIT
lane ran to completion and answered `Lint passed: all files clean` for

    fn area(width: i64, height: i64) -> i64:
        width * height
    fn main():
        print area(2, 3)
        print area(4, 5)

while the interpreter reports `warning[unnamed_duplicate_typed_args]`.
Instrumented: `signatures.len()` is 2 on both lanes, but
`_collect_indexed_call_replacements` (`lint_code.spl:82`, `Dict<text, i64>`
counters with `?? 0`) returns 0 rows under the JIT.

## Defect 4 — no diagnostic for `text` passed as `[text]` (OPEN, seed)

Neither lane rejects the defect-1 call. A type error at the call site would
have stopped the 2026-08-26 rewind at the first run.

## Mitigation landed with the fix

`src/compiler_rust/driver/src/exec_core.rs` `interpreter_preference_reason`
now returns `lint-jit-parity-unproven` for `src/app/cli/lint_entry.spl`, so
`lint` / `fix` / `fmt` run interpreted by default. An explicit
`SIMPLE_EXECUTION_MODE=jit` still reaches the JIT, which is how defects 2 and
3 are reproduced. Remove the pin only together with a lane-parity gate.

`scripts/check/check-pure-simple-lint-runnable.shs` gained the fixture above
and names a crashed fixture with its exit status. It already FAILED on the
broken tree; it is wired into no gate manifest, which is why nothing ran it.

## Until a seed carrying the pin is deployed

Already-deployed seeds take the JIT lane and exit 70 (defect 2) — loud, not
falsely green. Use `SIMPLE_EXECUTION_MODE=interpreter simple lint <file>`.

## Separate, pre-existing — lint aborts on `test_runner_main.spl` (OPEN)

`SIMPLE_EXECUTION_MODE=interpreter simple lint
src/app/test_runner_new/test_runner_main.spl` prints two warnings and then
`error: semantic: cannot iterate over this type: Nil` (rc=1, no verdict line).
Identical on the tree before this fix (`d6abe34243c`), so it is not caused by
the call-site change. No source location is reported; not root-caused.
