# Accessor Field-Access Tooling — Completion Plan (TL;DR)

Date: 2026-06-07 · Full: [accessor_fix_tooling_completion_plan.md](accessor_fix_tooling_completion_plan.md)

Status: **complete as of 2026-06-07**. The old 111 ACC001 field/accessor warning
target is cleared in current `origin/main`: full lint sweep reports `ACC001: 0`,
literal `field access` warnings `0`, and `accessor_fix_main.spl --quiet` reports
zero remaining safe rewrites.

**LSP sanity** passed for code-action kind, workspace edit, server capabilities,
and diagnostics specs.

**Tree-sitter sanity** passed for lexer, parser, token-kind, and tree specs.

**Accessor regression sanity** passed for dummy accessor fix, method-dispatch
field access, and compiler compile-options field-access specs.

```sdn
plan {
  status: "complete"
  field_warning_gate: "ACC001=0, field access warning text=0"
  accessor_fix_dry_run: "0 files, 0 wrappers, 0 call rewrites"
  lsp: "focused sanity specs pass"
  treesitter: "focused sanity specs pass"
}
```
