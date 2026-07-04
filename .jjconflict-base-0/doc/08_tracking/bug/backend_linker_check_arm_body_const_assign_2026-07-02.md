---
id: backend_linker_check_arm_body_const_assign_2026-07-02
status: OPEN
severity: low
discovered: 2026-07-02
discovered_by: `bin/simple check src/compiler/70.backend/linker/symbol_analysis.spl` while re-applying explicit dict-value type annotations
related: src/compiler/70.backend/linker/symbol_analysis.spl
related: src/compiler/10.frontend/core/parser_stmts.spl
---

# `bin/simple check` on backend/linker files hits unrelated "cannot assign to const 'arm_body'"

## Summary

`timeout 180 bin/simple check src/compiler/70.backend/linker/symbol_analysis.spl`
fails with `error: semantic: cannot assign to const 'arm_body'` and no
file/line location (plain text, `--json` and default modes both omit it).

This is unrelated to `symbol_analysis.spl` itself:

- The same error reproduces against the pre-fix (git HEAD) version of the
  file, so it is not caused by the `val sym: AnalyzedSymbol = ...` type
  annotations added in this pass.
- `bin/simple check src/compiler/70.backend/linker/__init__.spl` (which
  transitively includes `symbol_analysis.spl`) passes cleanly (warnings only,
  no error) — the failure is specific to invoking `check` with
  `symbol_analysis.spl` as the direct target file, which appears to pull a
  different/larger transitive module set than checking via `__init__.spl`.
- `arm_body` is a local variable name used in match-arm parsing in
  `src/compiler/10.frontend/core/parser_stmts.spl` (e.g. `val arm_body = parse_block()`
  around lines 861-967) — nothing in `symbol_analysis.spl` references it.
- The functional spec (`test/03_system/compiler/symbol_analysis_spec.spl`)
  passes 1/1, confirming `symbol_analysis.spl`'s actual logic is correct.

## Scope note

Blocks the literal "clean check" acceptance bar for
`symbol_analysis.spl` as a standalone target, but is a pre-existing,
unrelated compiler self-check quirk (likely in how `check <file>` resolves
transitive dependencies for backend/linker-layer files vs. `__init__.spl`
aggregation), not part of the 2026-07-02 "5 lost fixes" restoration.
