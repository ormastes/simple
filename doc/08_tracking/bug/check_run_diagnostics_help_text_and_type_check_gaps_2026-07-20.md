# `simple check`/`simple run` diagnostics: missing `help:` annotations + `check` not detecting type mismatches

**Date:** 2026-07-20
**Component:** `simple check` / `simple run` CLI diagnostics output
(`bin/release/x86_64-unknown-linux-gnu/simple`)
**Severity:** Medium-High — two distinct gaps in the same diagnostics
contract surface, both confirmed by direct fixture reproduction
**Found by:** whole-suite triage campaign, `test/02_integration/app/diagnostics/`

## Finding 1: `check`'s type checker does not detect an obvious type mismatch

`test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl`
seeds this fixture (`seed_type_mismatch_source`):

```simple
fn main():
    val x: i64 = "text"
```

and expects `simple check` on it to report a type-mismatch error (with a
stable code and `help:` text). Actual: `simple check` reports
`"status":"ok"`/`"All checks passed (1 file(s))"` — the obvious
`i64`-declared-assigned-a-string mismatch is not caught at all. Same for
the sibling return-type-mismatch fixture
(`fn value() -> bool: return 1`) — also reported as all-checks-passed.
4 of the file's 10 examples fail this way (2 text-output + 2 JSON-output
checks, for the two mismatch fixtures).

## Finding 2: `help:` annotation text is missing from file-not-found /
module-resolution error output

Both `check_diagnostics_contract_spec.spl` (2 examples: unresolved-import
warning, missing-file error) and
`test/02_integration/app/diagnostics/run_diagnostics_contract_spec.spl` (1
example: missing-file error on `run`) assert that the stable error/warning
text is followed by a `help:` line, e.g.:

- `= help: check the module path or add the source root with --source-root`
  (unresolved import)
- `= help: check that the path exists and is readable` (missing file, both
  `check` and `run`)

Actual output for the missing-file case (`run`):

```
error: compile failed: io: Cannot read "/tmp/simple_run_diagnostics_contract_missing.spl": No such file or directory (os error 2)
```

— no `help:` line at all. Same shape for `check`'s file-not-found and
unresolved-import paths: the primary error/warning text is present and
correctly worded, but the trailing `help:` guidance line that the contract
spec expects is absent.

## Finding 3 (smaller, same file): a warning-status example also fails

`check_diagnostics_contract_spec.spl`'s "prints stable warning code and
help in text output" example fails with `expected true to equal false` —
not yet isolated further; noted here rather than filed separately since
it's in the same contract file and may share Finding 1's root cause (the
checker's diagnostic-detection path).

## Affected specs

- `test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl`
  — 10/10 examples fail (Findings 1, 2, 3 combined)
- `test/02_integration/app/diagnostics/run_diagnostics_contract_spec.spl` —
  1/3 examples fail (Finding 2, missing-file case only; the division-by-zero
  stable-code example in the same file passes)

## Root-cause hypothesis

Not confirmed from source. Two independent-looking gaps: (1) the type
checker invoked by `simple check` isn't flagging a scalar type mismatch
that should be a hard error — possibly `check` runs a shallower pass than
full compilation, or the specific `i64 = "text"`/`-> bool: return 1`
patterns aren't wired into whatever check-mode uses; (2) the `help:`
annotation line is either not implemented for these two diagnostic codes or
was dropped in a refactor of the error-formatting path. Both are CLI/
diagnostics-formatting-level, not deep interpreter bugs; out of scope for a
Rust-seed source fix in this triage pass.

## Note

Both spec files are correct as written and left unmodified — the "never
weaken an assertion" rule applies; these are real coverage/contract gaps,
not stale test syntax.
