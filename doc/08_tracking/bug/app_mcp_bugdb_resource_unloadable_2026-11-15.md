# src/app/mcp/bugdb_resource.spl cannot load

Status: verification-pending
Severity: P3
Found: 2026-11-15

## Root cause

The app copy imported `app.mcp.resource_utils` (no such module) and used
`JsonBuilder`/`JsonArrayBuilder`, which the stdlib `resource_utils` does not
provide. It had no importers, so nothing noticed. The working implementation
(with the `bug_close_gate` enforcement) is
`src/lib/nogc_async_mut/mcp/bugdb_resource.spl`.

## Fix

The app module is now a thin re-export of the stdlib implementation.

## Specs

- Reproducer + prevention: `test/01_unit/app/mcp/bugdb_resource_loads_spec.spl`
  (case 1: loads and refuses a Closed transition without evidence; case 2,
  similar pattern: Fixed with nonexistent evidence refused, non-closing edit
  allowed, reader works). RED: executed=2 failed=2. GREEN: executed=2 passed=2.
- Runtime/native unqualified (seed interpreter, Windows).
