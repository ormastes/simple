# Lint modules still use facade wildcard imports and Bool/Int annotations (2026-10-30)

Status: open
Area: compiler/lint (_LintMain/*)

## Symptom

Four source-contract specs fail with `expected true to equal false`:

- `test/01_unit/compiler/lint/lint_config_model_primitive_types_spec.spl`
- `test/01_unit/compiler/lint/lint_checks_primitive_types_spec.spl`
- `test/01_unit/compiler/lint/traceability_primitive_types_spec.spl`
- `test/01_unit/compiler/lint/lint_remaining_primitive_types_spec.spl`

## Root cause

The specs pin a refactor of the `_LintMain` modules that never landed on release/1.0. The specs
arrived with the 2026-09-29 transplant `88aac2ffe28`. The refactor exists only on unmerged
2026-08-17 commits (for example `7644fbdea88`). It requires:

- no `use compiler.tools.lint.main.*` facade wildcard import inside `_LintMain/*`, with concrete
  owner imports instead
- `bool` / `i64` instead of `Bool` / `Int` (for example `config_and_model.spl:894` and
  `:1251-1257`)
- new imports such as `traceability_and_assertions.{indent_width}` in `name_lints.spl` and
  `os_freestanding_lints.spl`

Removing the facade wildcard from six mutually importing modules risks import cycles under the seed
interpreter. That makes this a module-structure change, not a spec fix.

## Unblock

Land the `_LintMain` import and annotation refactor. Then remove the `pending` markers that link
here.
