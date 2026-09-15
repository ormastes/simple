# SPipe Docgen Blocked By Flat AST Bridge Parse Error

## Closed 2026-09-13 — Does not reproduce: the file that failed to parse no longer exists and docgen processes the spec

- **measured** `bin/simple-interp spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl -o <dir>` printed `Processing specs:` then `OK ide_office_plugin_suite_spec (106 lines)` — no parse error.
- **measured** `src/compiler/10.frontend/flat_ast_bridge_part2.spl`, the file named in the reported error, is gone; only `flat_ast_bridge.spl` remains.
- **measured** The run does end `EXIT=139` after emitting the doc — a separate teardown crash, not the reported parse failure; file it separately if it blocks the gate.
- **inferred** With the offending source file deleted and the spec generating cleanly, the flat-AST-bridge parse blocker is closed.


Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

## Date
2026-06-01

## Context
Regenerating `doc/06_spec/system/app/ide/feature/ide_office_plugin_suite_spec.md` for the IDE office plugin suite updated the manual content, but the docgen command exited nonzero because the current dirty worktree has an unrelated compiler parse error.

## Reproduction

```bash
bin/simple-interp spipe-docgen test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl -o doc/06_spec
```

Observed failure:

```text
error: compile failed: parse: in "/home/ormastes/dev/pub/simple/src/compiler/10.frontend/flat_ast_bridge_part2.spl": Unexpected token: expected expression, found Else
```

## Impact
The IDE generated manual currently includes all nine scenarios, but the docgen command cannot be treated as a clean verification gate until the unrelated compiler parse error is fixed.
