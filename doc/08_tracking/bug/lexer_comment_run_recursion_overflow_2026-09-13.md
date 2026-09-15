# CoreLexer recursed once per skipped line — a long comment banner killed the whole test runner

- Status: FIXED (2026-09-13)
- Binary: `/home/yoon/dev/cargo-fulltest/release/simple`, sha256 `4dfdf671742007d30210` (Rust seed built 2026-09-13 16:00)
- Base: `origin/main` `f4cd1c306dd`
- Area: `src/compiler/10.frontend/core/lexer_struct.spl` (`CoreLexer.handle_indentation`)
- Spec: `test/01_unit/compiler/frontend/lexer_comment_run_recursion_overflow_spec.spl`

## Symptom

`bin/simple test test/01_unit` and `bin/simple test test/01_unit/compiler/hir`
both aborted the RUNNER PROCESS mid-sweep:

```
[route] mode=interpreter
error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'peek'
```

The sweep exited rc=1 with no summary. Measured 2026-09-13: the hir directory
holds 165 spec files; only 85 ever reported a verdict (33 PASS / 52 FAIL) and
the remaining 80 were never run and never counted. The whole-tree
`test/01_unit` run died the same way after 179 verdicts.

## Root cause

`CoreLexer.handle_indentation()` (`lexer_struct.spl`) ended both of its
skip branches with `self.scan_token(); return`:

- blank / whitespace-only line: `advance(); at_line_start = true; scan_token()`
- comment-only line: skip to newline; `advance(); at_line_start = true; scan_token()`

`scan_token()` re-enters `handle_indentation()` for the next line, so a run of
N consecutive skippable lines cost N nested interpreter frames — the stack only
unwinds when a real token is finally produced. The seed interpreter's recursion
guard (`push_call_depth`, `interpreter_state.rs:791`, limit 1000) rejects call
1000, so roughly 450 consecutive comment lines abort the process.

`peek` in the message is a red herring: `CoreLexer.peek()`
(`lexer_struct.spl:209`) is a three-line non-recursive accessor. It is simply
the innermost call the depth guard happened to reject. That misdirected the
first three investigations.

Why it takes the RUNNER down rather than a child: the runner lexes every spec's
SOURCE in its own process — `run_test_file_interpreter` →
`preprocess_spipe_file` → `simple_code_lines`
(`src/compiler/10.frontend/core/source_facts.spl`, which drives the real
CoreLexer) — and `run_test_file_interpreter` sets
`SIMPLE_EXECUTION_MODE=interpret` on itself first, so that in-process lexing
runs under the interpreter (and therefore under the depth guard) instead of the
JIT. One banner-heavy spec therefore kills the sweep.

This is also why a single-file run of the offending spec does NOT reproduce:
without the sweep's env state the probe is JIT-compiled and the guard never
runs.

## Minimal repro (interpreter mode is required)

```
$ cat probe.spl
use compiler.frontend.core.source_facts.{simple_code_lines}
fn build(n: i64) -> text:
    var s = ""
    var i = 0
    while i < n:
        s = s + "# c\n"
        i = i + 1
    s + "fn main():\n    print(1)\n"
fn main():
    var n = 100
    while n <= 800:
        print "n={n} lines={simple_code_lines(build(n)).len()}"
        n = n + 100

$ SIMPLE_EXECUTION_MODE=interpret bin/simple run probe.spl
n=100 lines=103
n=200 lines=203
n=300 lines=303
n=400 lines=403
error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'peek'
```

Without `SIMPLE_EXECUTION_MODE=interpret` the same probe prints all eight rows —
the JIT path does not go through the recursion guard, so any in-process
assertion would pass vacuously. The spec shells out with the env var set for
exactly that reason.

Only one spec in `test/01_unit/compiler/hir` carries a run over the threshold:
`hir_lowering_spec.spl`, 638 consecutive comment lines.

## Fix

`handle_indentation()` now consumes a run of skippable lines in a `while` loop
instead of recursing. The two cases `scan_token()` handles itself before
delegating back — end of input, and a line whose first character is the newline
— still go through `scan_token_rescan()`, so the emitted token stream is
unchanged; those branches always emit a token (or run their own bounded
continuation handling) and return, so their one frame does not accumulate.

## Evidence

RED (before):  `2 examples, 1 failure` — the 600-line example fails on
`captured.contains("stack overflow")`; the 40-line control passes.
GREEN (after): `2 examples, 0 failures`.

No regression in the neighbouring lexer specs (run before and after):
`core_source_facts_spec` 1/0, `lexer_dead_stream_forward_progress_spec` 6/0,
`lexer_if_condition_leading_and_continuation_spec` 4/0,
`lexer_indentation_eof_emits_token_spec` 6/0,
`lexer_position_unification_spec` 4/0.
`lexer_snapshot_spec` reports `5 examples, 2 failures` both WITH and WITHOUT
this change (verified by restoring `HEAD:lexer_struct.spl` and re-running) — a
pre-existing red, not caused here.
