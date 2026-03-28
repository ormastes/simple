---
name: TODO Comment Format Reference
description: TODO/FIXME comment format spec, priority levels, areas, lint rules, skip_todo, todo-scan
type: reference
---

## Format
```
TODO: [area][P0|P1|P2|P3] description [#issue] [blocked:#n,#m]
FIXME: [area][priority] description [#issue] [blocked:#n,#m]
```

## Priority: P0 (critical), P1 (high), P2 (medium), P3 (low)

## Areas
runtime, codegen, compiler, parser, type, stdlib, gpu, ui, test, driver, loader, pkg, doc

## Examples
```simple
# TODO: [stdlib][P0] Implement via FFI [#234]
# FIXME: [runtime][P1] Fix memory corruption [#567] [blocked:#100]
```

## Lint Rules (T001-T004)
- T001 Warn: missing format. T002 Warn: invalid area. T003 Warn: invalid priority
- T004 Deny: P0/critical must have issue number

## Skip: `#![skip_todo]` or `<!-- skip_todo -->` for files that discuss TODO format

## Commands
```bash
bin/simple todo-scan    # Scan + generate doc/TODO.md + doc/tracking/todo/todo_db.sdn
bin/simple todo-gen     # Generate docs only (legacy)
```

## Regex
```regex
(TODO|FIXME):\s*\[(\w+)\]\[(\w+)\]\s*(.+?)(?:\s*\[#(\d+)\])?(?:\s*\[blocked:(#\d+(?:,#\d+)*)\])?$
```
