# SPL-doctest phase exits non-zero with NO verdict line when a source file fails to compile

## 2026-11-09 verification (p3-mine lane) — FIXED on release/1.0.0

The abort-without-verdict shape no longer exists: `run_spl_doctest_mode`
(`src/lib/nogc_sync_mut/test_runner/test_runner_modes.spl`) never loads or
compiles Simple sources in-runner anymore — each doctest block is compiled and
executed by a pinned child binary (`run_spl_doctests_same_file`,
`src/lib/nogc_sync_mut/test_runner/doctest_runner.spl`), and both the single
runner (`src/app/test_runner_new/test_runner_single.spl:1246`) and the main
runner (`src/app/test_runner_new/test_runner_main.spl:1641`) print
`SPL Doctest: N passed, N failed, N skipped` unconditionally after it returns.

Measured on the seed binary (`src/compiler_rust/target/bootstrap/simple`,
`simple test --spl-doctest`, worktree at origin/release/1.0.0):

| fixture | verdict line | exit |
|---|---|---|
| passing doctest | `1 passed, 0 failed, 0 skipped` | 0 |
| doctest code that fails to compile | `0 passed, 1 failed, 0 skipped` + per-block error line | 1 |
| doctest in an uncompilable source file | `0 passed, 1 failed, 0 skipped` + per-block error line | 1 |
| sweep dir with one good + one bad file | `1 passed, 1 failed, 0 skipped` | 1 |

A run that now produces no verdict line is a crash of the runner binary
itself, which no in-SPL change can annotate; the filed load-failure class is
closed. The suggested `ABORTED` wrapper targeted the old in-runner load path
and is obsolete. Bug-db row set `fixed` with this evidence.

- **Filed:** 2026-08-25
- **Status:** OPEN
- **Class:** the repo's known "no verdict line = UNKNOWN" defect family
  (cf. `killed_spec_emits_no_verdict_line_2026-08-09.md`,
  `directory_lane_emits_no_verdict_line_2026-08-10.md`,
  `guard_silent_nonzero_exit_no_verdict_line_2026-08-17.md`)

## Symptom

The `--spl-doctest` phase can exit 1 having printed its START banner but **no**
`SPL Doctest: N passed, N failed, N skipped` line at all:

```
=== Running SPL Doctests ===

SPL Doctest: Running doctests from 1 source file(s)...
error[E1002]: function `unsafe` not found
  = help: check the function name or import the module that defines it
```

and, from a different cause on a rebuilt seed:

```
error: compile failed: parse: in ".../src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl": Unexpected token: expected Colon, found If
```

In both cases the run aborts while loading Simple sources, before any block is
executed, and dies without a verdict.

## Why it matters

Per `.claude/rules/testing.md` a run with no verdict line ABORTED and its counts
are UNKNOWN — not pass, not fail. But the ONLY thing distinguishing this from a
completed run is the ABSENCE of a line. Anything that greps for a `FAIL` marker,
or counts failures, or diffs two runs, reads an aborted run as a clean one.

This is not hypothetical. A whole-suite figure of `267 passed, 215 failed` was
carried across a day of work as the doctest baseline while the phase was in fact
aborting on the then-deployed seed, and two independent lanes had to re-derive
that their measurements were void.

The recent test-runner work (`cd9dfa107d4`, `f910634dc3c`) established exactly
this invariant for the main runner — a run that executed zero specs must not
emit a `Results:` line, and a run with no `Results:` line aborted. The doctest
phase needs the same treatment from the other direction: it should emit an
explicit ABORTED verdict rather than nothing.

## Suggested fix

`run_spl_doctests_*` in `src/lib/nogc_sync_mut/test_runner/test_runner_modes.spl`
(the banner is printed at :75) should wrap the per-file load so that a compile
failure while loading sources produces a distinguishable terminal line, e.g.

```
SPL Doctest: ABORTED — <n> file(s) not loaded: <first error>
```

so that a machine reading the output can tell "aborted" from "completed", and
never has to infer it from silence. A guard that asserts the phase printed
exactly one terminal verdict line would pin it.

## Related

- `deployed_seed_cannot_parse_value_b