# SPL-doctest phase exits non-zero with NO verdict line when a source file fails to compile

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

- `deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25.md` — one cause.
- `spl_doctest_composite_fails_wildcard_reexport_modes_2026-08-25.md` — a
  neighbouring doctest-harness defect found in the same investigation, where the
  failure reason is rendered as a bare source span with the message dropped.
