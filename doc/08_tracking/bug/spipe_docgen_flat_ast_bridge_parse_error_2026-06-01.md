# SPipe Docgen Blocked By Flat AST Bridge Parse Error

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
