# Parsed-revision lint entry resets the caller's AST arena (2026-10-30)

Status: open
Area: compiler/lint (entry_and_fixes.spl, param_object_rules.spl)

## Symptom

`test/01_unit/compiler/lint/lint_parsed_revision_entry_spec.spl`, example "preserves parser state
while consuming matching declarations", reports one `LINTREV001` for a revision with a matching
path and digest.

## Root cause

`lint_cli_source_with_parsed_revision` (`entry_and_fixes.spl:199`) promises that it "never invokes
or resets the parser/AST arena". It calls `linter.lint_source_for_parsed_append` first. That runs the
static rule table, and the `param_object` rule calls `parse_module_silent_checked` twice
(`src/compiler/90.tools/lint/param_object_rules.spl:38` and `:173`). Each call resets the arena.

A probe measured `ast_generation()` going 0 -> 2 across `lint_source_for_parsed_append`. As a
result:

- the generation check rejects every real revision
- skipping or reordering that check would consume stale declaration indices

## Unblock

Give rules that need declarations the caller's parsed revision (for example via `LintUnit`), or let
them fall back to their own parse only when no revision is active. Then remove the `pending` marker
that links here.
