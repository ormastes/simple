# `simple lint` aborts with `class CodeLine has no field named code`, depending on the linted file's import closure

Date: 2026-09-07
Severity: MEDIUM (the linter cannot process affected files at all — it is not a finding, it is an abort)
Status: FIXED (2026-11-11, lane ne13) — fixing commit eea2a322ac74; verified on release/1.0.0 tip, see addendum
Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, 50093192 bytes, mtime 2026-09-06 09:59:11)

## Symptom

`sh scripts/check/lint-cached.shs <file>` ends:

```
error: semantic: class `CodeLine` has no field named `code`
FAIL — 1 file(s) checked, 1 with findings
```

The verdict says "1 with findings", but there is no finding: the linter aborted
during semantic analysis of its own passes. `CodeLine`
(`src/compiler/35.semantics/lint/lint_text.spl:10`) is a private class with
fields `line_num`, `raw`, `trimmed` — it has no `code` field and nothing in that
file reads one. Many sibling lint passes declare their OWN finding class with a
`code: text` field (`argument_count.spl:31`, `bare_primitive_internal.spl:47`,
`closure_capture.spl:52`, …), which is the shape of the
`compiler_cross_module_private_symbol_collision` warning this compiler already
emits for functions.

## It depends on the linted file's import closure, not on its content

Measured on the same binary, same session:

| linted file | verdict |
|---|---|
| `src/lib/common/contracts/orchestration/ci_v1.spl` | PASS, clean |
| a 4-line file whose only import is `std.common.contracts.orchestration.ci_v1.{CI_API_VERSION_V1}` | **abort** |
| a 5-line file whose only import is `app.io.mod.{file_read}` | PASS |
| `src/lib/common/sdn/parser.spl` (working tree) | **abort** |
| `src/lib/common/sdn/parser.spl` at `origin/main`, byte-for-byte, linted from a temp path | PASS |
| `src/app/ci/pipeline_runner.spl` | **abort** |

The second row is the decisive one: content that lints clean makes a *different,
trivial* file abort merely by being imported. So the trigger is which modules get
co-compiled into the lint session, not any construct in the file under lint.

`lint_text.spl` itself is unmodified and identical to `origin/main`.

## Consequence

Any lane whose files reach the affected closure cannot get a lint verdict at all.
The failure mode is worse than a false finding because the verdict line still
says "1 with findings", so a caller that only reads the last line records a
quality failure against innocent code.

## Suspected cause

Private-symbol name collision across co-compiled lint modules resolving
`CodeLine` to the wrong declaration — the same class of defect the compiler warns
about for functions (`public function X has 2 co-compiled definitions …`) but
does not warn about for classes.

## Repro

```bash
printf 'use std.common.contracts.orchestration.ci_v1.{CI_API_VERSION_V1}\n\nfn probe() -> text:\n    CI_API_VERSION_V1\n' > /tmp/p.spl
sh scripts/check/lint-cached.shs /tmp/p.spl   # -> error: semantic: class `CodeLine` has no field named `code`
```

## Workaround

None for the affected files. Lint verdicts for
`src/app/ci/pipeline_runner.spl` and `src/lib/common/sdn/parser.spl` are recorded
as BLOCKED-by-linter in `.spipe/simple_orchestrator/state.md`, not as PASS and
not as findings.

## Addendum 2026-11-11 (lane ne13) — FIXED, verified on release/1.0.0

**Fixing commit:** `eea2a322ac74` "fix(lint): read CodeLine.trimmed in
linear_scan_in_loop" (2026-10-09) — the abort came from a lint rule reading a
nonexistent `cl.code` on `CodeLine` (which has only `line_num`/`raw`/`trimmed`);
the rule now reads `.trimmed` and skips comment-only lines, with a spec case
added. Companion `b41d64cad69d` pinned lint to the interpreter lane.

**Verification actually run** (seed-smoke, worktree simple-p3-ne13-20261111,
tip c8b6d0ebe90e, fresh seed 46fe8f6b6def via
`sh scripts/check/lint-cached.shs`, SIMPLE_LIB=src):

| probe (from this doc's own repro table) | 2026-09-07 verdict | today |
|---|---|---|
| 4-line file importing only `std.common.contracts.orchestration.ci_v1.{CI_API_VERSION_V1}` | abort (`CodeLine has no field named code`) | **PASS, clean** (0 cached, 1 linted) |
| `src/lib/common/sdn/parser.spl` (was: abort even at origin/main) | abort | **PASS, clean** (46 warnings, 0 errors) |
| `src/app/ci/pipeline_runner.spl` | abort | **lints to completion**: 2 `error[primitive_api]` (bare `bool` in public API at :290) + 5 warnings — real findings, no abort |

The linter no longer aborts on any of the three recorded closures; the "verdict
says findings but there are none" misreport shape is gone. The remaining
`pipeline_runner.spl` `primitive_api` findings are ordinary lint output for the
file's authors, not this defect. The `.spipe/simple_orchestrator/state.md`
BLOCKED-by-linter entries for these two files can be re-lifted by their owner.
