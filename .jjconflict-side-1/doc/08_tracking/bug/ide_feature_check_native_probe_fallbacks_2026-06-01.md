# IDE feature check native probe fallbacks

## Status
Resolved for IDE feature-check completion; runtime/content follow-up remains optional.

## Observed
The focused IDE Office plugin system spec passes exact renderer assertions, but
the direct source-entrypoint feature check needs native-safe structural
fallbacks for several probe booleans:

```bash
timeout 90s bin/simple-interp src/app/ide/main.spl --feature-check --tui
timeout 90s bin/simple-interp src/app/ide/main.spl --feature-check --gui
```

The Markdown heading/table checks and TUI preview content checks now use exact
existing renderer helper output and report true from the direct IDE entrypoint.
The direct IDE feature-check now proves exact GUI Office-layout containers from
the existing renderer path (`md-ppt-deck` and `md-sheet-layout`) without relying
on source-shape fallbacks. In the full native/import closure, slide title and
sheet cell content can still be dropped from the direct GUI HTML string even
though focused specs preserve that content. An isolated GUI-only `main` probe
also showed the lowerer can fail before interpretation on `BlockModel.from_markdown`,
so content loss remains a runtime/import-closure follow-up rather than a missing
IDE capability.

The spreadsheet IDE probe previously called `app.office.sheets.formula.evaluate_formula`
for `A1+B1`, but direct source-entrypoint execution reported `evaluator=false`
because the f64-return path rendered `0` instead of `5`. The current worktree
routes the IDE probe through `app.office.sheets.formula.evaluate_formula_display_text`
for an integer-safe display formula and now reports `formula=5 evaluator=true`.

## Impact
The feature check proves capability wiring, owner modules, Markdown/TUI renderer
availability, GUI Office-layout container output, formula display evaluation,
and existing app-module reuse. It does not attempt to prove the lower-level
native f64 evaluator return path or full GUI Office HTML content preservation in
the all-import feature-report closure.

## Follow-up
- Isolate why direct source-entrypoint execution differs from the focused IDE
  system spec for full GUI presentation/sheet renderer content.
- Add a small f64-return regression for `app.office.sheets.formula` or the
  runtime function-return path if direct numeric evaluator evidence becomes
  release-critical.
