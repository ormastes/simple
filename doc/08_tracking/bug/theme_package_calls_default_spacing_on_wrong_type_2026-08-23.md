# `theme_package.spl:654` calls `Spacing.default_spacing()`, a method that type does not have

Date: 2026-08-23. Found by the in-development tag sweep of `test/01_unit/`
(`doc/09_report/in_development_sweep_unit_2026-08-23.md`), while classifying a
failing spec to decide whether it was unfinished feature work. It was not — the
spec is correct and the source is wrong.

## Defect

`src/lib/nogc_sync_mut/ui/theme_package.spl:654`

```
val spacing = Spacing.default_spacing()
```

`default_spacing()` is declared as a static on **`IOSSpacingScale`**:

- `src/lib/common/ui/design_tokens.spl:199` — `static fn default_spacing() -> IOSSpacingScale:`
- `src/lib/common/ui/design_tokens.spl:241` — the only correct call site,
  `spacing: IOSSpacingScale.default_spacing(),`

`Spacing` is a *different* type, an enum declared at
`src/lib/common/ui/design_tokens.spl:3`. It has no `default_spacing` member, so
the call at `theme_package.spl:654` cannot resolve.

## Evidence

`test/01_unit/app/ui_web/html_css_theme_authority_spec.spl` — 1 of 6 examples
passed, 5 failed, every failure reporting:

```
semantic: unknown variant or method 'default_spacing' on enum Spacing
```

Reproduce:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/app/ui_web/html_css_theme_authority_spec.spl
```

Read the final `Results:` line only; the run prints a large volume of
`[gc-warning]` lines first.

## Why this is filed rather than tagged

The sweep that found it exists to apply `@tag:in-development` to specs whose
feature is not written yet. This is the opposite case: the capability
(`default_spacing`) **is** implemented, on `IOSSpacingScale`, and one call site
already uses it correctly. The spec is asserting real, correct behaviour that a
mistyped call site breaks. Per `.claude/rules/testing.md` a spec that correctly
asserts a defect stays RED with a bug record — neutralising it with the tag
would have hidden a live defect in shipped stdlib UI code.

## Unblock condition

Decide which type the caller actually wants and fix
`src/lib/nogc_sync_mut/ui/theme_package.spl:654` accordingly — most likely
`IOSSpacingScale.default_spacing()`, matching `design_tokens.spl:241`. If
`Spacing` genuinely needs its own default, add it to the enum at
`design_tokens.spl:3` instead.

Per the two-spec rule, the fix ships with the reproducing spec above plus a
generalization spec probing sibling `design_tokens` statics for the same
wrong-receiver shape.

## Status

OPEN. Left RED deliberately.
