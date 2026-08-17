# Bug: `simple lint` fails on any file containing a `class` — "method `get` not found on type `str`"

- **Date:** 2026-07-27
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** high (lint unusable as a lane gate for class-bearing OS sources)
- **Found by:** two independent SimpleOS harden lanes (P1 IPC, P3 VFS) on untouched control files

## Symptom
`bin/simple lint <file>` (seed binary copy) on ANY `.spl` file that contains a
`class` declaration errors:

```
method `get` not found on type `str` (receiver value: <ClassName>)
```

Reproduced on untouched `src/os/kernel/ipc/capability.spl`,
`src/os/kernel/ipc/l4_fast_ipc.spl`, and a control file under
`src/os/kernel/fs/` — not caused by new lane code.

## Trace
Points into
`src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:495,535` —
a class-name value is flowing into a Dict/`get` call that expects `str`.

## Impact
Lint cannot gate any lane whose sources use classes (most of src/os). Lanes
fell back to spec runs as the quality gate.

## Root cause (corrected)
The trace file attribution above was WRONG. Line 535 is in
`src/compiler/90.tools/lint/_LintMain/lint_checks.spl`, not
`traceability_and_assertions.spl` — both files open with the same header and are
merged into one `impl Linter`, so the diagnostic named the wrong sibling. There
was no Dict involved either; the "receiver value: <ClassName>" text is a
diagnostic-formatting artifact.

The actual defect: `Linter.is_pascal_case` did

```
val first_char = name.get(0)
match first_char:
    case Some(c): c.is_uppercase()
    case nil: false
```

`String` has no `get(index)` method. `is_pascal_case` has exactly one caller —
the `ST002` class-name check in `check_line` (`lint_checks.spl:368`), reached by
every line starting with `class `. So any file declaring a class aborted the
whole lint run; struct-only files were unaffected. Content-independent, which is
why `git show HEAD:` copies of untouched files reproduced it.

## Fix
`lint_checks.spl:535` — replace the non-existent `.get(0)` with a slice + case
comparison:

```
val first_char = name.slice(0, 1)
first_char == first_char.upper() and first_char != first_char.lower()
```

The second conjunct matters: a non-cased first char (digit, `_`) has
`upper() == lower()`, so it correctly reports false instead of true.
Verified directly: `ValidName`→true, `invalid_name`/`9abc`/`_Foo`/``→false.

## Verification
- `mnf` (method-not-found) count 1 → 0 on `database/core.spl`, `database/wal.spl`,
  `os/services/pm_service.spl`, and a minimal 2-line `class` repro.
- Findings that appear "new" after the fix are checks the aborted run never
  reached (5 `non_exhaustive_match`, 2 `unnamed_duplicate_typed_args`, `D001`,
  `COLL006` on core.spl) — that is the payoff, not a regression. `COLL006` here
  is a separate false positive, filed in
  `lint_coll006_false_positive_substring_scan_loop_2026-07-27.md`.
- Regression spec: `test/01_unit/app/lint_spec.spl` — two tests, both pass.

## Note: ST002 is off by default
`ST002` maps to the `style_convention` lint group, which is `Allow` (off) by
default, so it is filtered out of `lint_source` results. An end-to-end assertion
on ST002 emission therefore cannot work; the regression spec asserts on
`is_pascal_case` directly instead.
