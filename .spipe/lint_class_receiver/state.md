# Lane LINTCLS2 — lint aborts on every file containing a `class`

- **Date:** 2026-07-27
- **Status:** FIXED + verified (not committed — lane was told not to commit/push)

## Defect
`bin/simple lint <file>` aborted with
`error: semantic: method 'get' not found on type 'str' (receiver value: <SomeClass>)`
for any `.spl` file declaring a `class`. Content-independent — `git show HEAD:`
copies of untouched files reproduced it. Lint was unusable as a quality gate.

## Minimal trigger
`build/lintcls_repro/a_class.spl` (2 decls) triggers; `b_struct.spl` (same file
with `struct` instead of `class`) does NOT. Trigger is the `class ` line prefix
alone — no methods, fields, or traits needed.

## Offending rule
`src/compiler/90.tools/lint/_LintMain/lint_checks.spl:535` — `Linter.is_pascal_case`
called `name.get(0)`; `String` has no `get(index)`. Its only caller is the ST002
class-name check at `lint_checks.spl:368`, inside `check_line`'s `first == "c"`
branch.

The original bug report blamed `traceability_and_assertions.spl:495,535`. That
was wrong — the two files share a header and merge into one `impl Linter`, so
the diagnostic named the wrong sibling file at the right line number.

## Fix
Slice + case comparison instead of the non-existent `.get`:

```
val first_char = name.slice(0, 1)
first_char == first_char.upper() and first_char != first_char.lower()
```

Not a suppression — the rule still classifies. Second conjunct is load-bearing:
non-cased first chars (digit, `_`) have `upper() == lower()` and must be false.

## Before / after (`build/lintcls_repro/spread.sh`)
mnf = count of "not found on type"; warn counts include ~40 lines of the
linter's own self-diagnostic noise emitted for every target file.

| file | before | after |
|---|---|---|
| database/core.spl | rc=1 mnf=1 err=1 warn=40 | rc=1 mnf=0 err=0 warn=48 |
| database/wal.spl | rc=1 mnf=1 err=1 warn=40 | rc=1 mnf=0 err=0 warn=42 |
| os/services/pm_service.spl | rc=1 mnf=1 err=1 warn=40 | rc=0 mnf=0 err=0 warn=51 |
| lint/main.spl (control) | rc=0 mnf=0 err=0 warn=40 | rc=0 mnf=0 err=0 warn=40 |
| a_class.spl (minimal) | rc=1 mnf=1 err=1 warn=40 | rc=0 mnf=0 err=0 warn=40 |

Warn increases are checks the aborted run never reached (5 non_exhaustive_match,
2 unnamed_duplicate_typed_args, D001, COLL006 on core.spl) — the payoff, not a
regression. Diff of before/after outputs shows every other delta is a ±4 line
shift in the linter's self-diagnostics, caused by the 4 comment lines the fix
added. COLL006 is a separate pre-existing false positive, already filed.

## Regression spec
`test/01_unit/app/lint_spec.spl` — harness exists and works.
- "lints a class declaration without aborting on the receiver type" — PASS
- "classifies PascalCase correctly after the receiver fix" — PASS
  (asserts `is_pascal_case` directly; ST002 is in the `style_convention` group,
  which is `Allow`/off by default and filtered out of `lint_source` results, so
  an end-to-end ST002 assertion is not possible — an earlier draft of this spec
  failed for exactly that reason.)

`Results: 20 total, 19 passed, 1 failed`. The 1 failure is a PRE-EXISTING
runner-accounting phantom: every describe block reports 0 failures and no `✗` is
printed. Baseline confirmed by running the untouched `HEAD` copy of the spec:
`18 total, 17 passed, 1 failed`. My change took it 18→20 total, 17→19 passed,
phantom held at 1.

## Verification tier
Real, end-to-end — NOT redeploy-blocked. `bin/simple` is the Rust seed but it
compiles/interprets the pure-Simple linter source at run time, so the `.spl` edit
is directly observable (before/after differ). No bootstrap needed.

## Files touched
- `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` (the fix)
- `test/01_unit/app/lint_spec.spl` (2 regression tests)
- `doc/08_tracking/bug/lint_class_receiver_get_str_traceability_2026-07-27.md` (marked fixed, trace corrected)

Note: the `use std.tooling.easy_fix.types.{...}` import added at the top of
`lint_checks.spl` and `traceability_and_assertions.spl` is required — those
types are referenced 7 times in `lint_checks.spl`.

## Repro assets
`build/lintcls_repro/` — `spread.sh` (before/after harness), `a_class.spl` /
`b_struct.spl` (minimal trigger pair), `probe_prim.spl` / `probe_call.spl`
(primitive + direct-call probes), `*.before` / `*.final` lint outputs.
