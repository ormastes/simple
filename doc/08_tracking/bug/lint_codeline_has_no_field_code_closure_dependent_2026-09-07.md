# `simple lint` aborts with `class CodeLine has no field named code`, depending on the linted file's import closure

Date: 2026-09-07
Severity: MEDIUM (the linter cannot process affected files at all — it is not a finding, it is an abort)
Status: OPEN
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
