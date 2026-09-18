# `LintRunResult.has_easy_fix()` disagrees with a direct `match` on the same field

- Date: 2026-09-18
- Status: OPEN (worked around, not fixed)
- Component: `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
  (`has_easy_fix`, line 1164) vs.
  `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`
  (`_run_lint_with_linter_source`'s per-diagnostic fix counter, workaround at
  line 1215)

## Symptom

`LintRunResult.has_easy_fix()` is defined as:

```simple
fn has_easy_fix() -> Bool:
    self.lint.easy_fix.? == true
```

`self.lint.easy_fix` is `EasyFix?` (an `Option<EasyFix>`/nilable field). For a
diagnostic that genuinely carries `Some(fix)` — the exact `LintDiag.easy_fix`
value the per-diagnostic `.format()` line reads to print `fix: available` —
`has_easy_fix()` was observed to still read as false-ish: the per-file fix
counter in `_run_lint_with_linter_source` that used to call
`effective_item.has_easy_fix()` stayed at 0 for a file carrying a real COLL020
Certain fix, even though the SAME diagnostic's `.format()` output on the very
same line correctly printed `fix: available`. The two readings of the identical
`LintDiag.easy_fix` field disagreed within the same function call.

Effect: `--fix` / `--fix-dry-run`'s `fix_count > 0` gate
(`_run_lint_with_linter_source`, guarding the call to `apply_collected_fixes`)
never opened, silently disabling `simple lint --fix`/`--fix-dry-run` for every
real COLL002/COLL020 fix ever produced through that path — while `simple fix`
(a separate CLI, `src/app/cli/fix_entry.spl` -> `fix/main.spl`) was unaffected,
since it calls `collection_002_fix`/`collection_020_fix` directly and does its
own `match ... case Some/nil` rather than going through `has_easy_fix()`.

## Repro

Any source that trips a Certain COLL002 or COLL020 fix (e.g. the
`COLL020_FIX_SRC` fixture in
`test/01_unit/compiler/lint/collection_easy_fix_spec.spl`) run through
`simple lint --fix-dry-run`: the per-diagnostic line reports
`fix: available (safe)`, but before the workaround below, `fix_count` in the
same request stayed `0` and the `--fix-dry-run` gate never ran.

No COLL rule carried a real (non-nil) `easy_fix` before the COLL002/COLL020
Certain-fix lane landed (`7ab671e7813` had removed the one prior
`collection_easy_fix` for a different reason), so this path was structurally
never exercised until this lane — it is not a regression in previously-working
code, it is a latent defect the current lane's fixtures were the first thing to
reach.

## Where it is worked around

`entry_and_fixes.spl`, `_run_lint_with_linter_source`, around line 1215: the
per-diagnostic fix counter now matches `effective_item.lint.easy_fix` directly
(`case Some(_): fix_count = fix_count + 1` / `case nil: ...`) instead of
calling `effective_item.has_easy_fix()`. This is a call-site workaround only —
`has_easy_fix()` itself is untouched and any other caller of it (if one is ever
added) will hit the same disagreement.

## Not yet root-caused

The exact reason `self.lint.easy_fix.? == true` disagrees with a direct
`match self.lint.easy_fix: case Some(_) / case nil` on the same field value has
not been isolated to a minimal repro outside the lint pipeline (e.g. whether
`.?` on an `Option<T>` field returns something other than a plain presence
check, or whether `== true` against whatever `.?` yields is the actual defect).
That isolation, and a real fix to `has_easy_fix()` itself, are still open.
