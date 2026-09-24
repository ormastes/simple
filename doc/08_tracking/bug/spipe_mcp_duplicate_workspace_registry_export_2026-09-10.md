# SPipe MCP package: duplicate workspace-registry export

- **Date:** 2026-09-10
- **Status:** fixed by `spipe_mcp_export_linux`
- **Severity:** P1 (the package unit suite cannot load workspace-backed modules)
- **Area:** `examples/05_stdlib/spipe/src/workspace/registry.js`

## Pre-fix reproduction

From `examples/05_stdlib/spipe` on the Linux-compatible Node path:

```text
node --test test/unit/*.js
```

The suite failed while loading several tests with:

```text
SyntaxError: Identifier 'isWorkspaceRegistryV1' has already been declared
```

The owner module contains three declarations: the original WeakSet brand
predicate at line 15 and two later composition-root predicates at lines 298 and
304. The latter pair also refer to stale, undefined registry sets.

## Boundary and plan

This is a pure JavaScript export-surface defect. The canonical owner is the
WeakSet brand predicate; no compiler or Rust/runtime change is implicated.
The fix removes only the stale duplicate declarations and adds an import/load
regression plus an adjacent direct brand-contract assertion.
