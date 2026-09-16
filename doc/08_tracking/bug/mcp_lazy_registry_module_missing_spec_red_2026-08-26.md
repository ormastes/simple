# mcp lazy-loading spec red: `mcp_lib` modules no longer exist (2026-08-26)

## Symptom
`test/01_unit/lib/mcp/lazy_loading_spec.spl` fails at HEAD with:

```
error: semantic: Cannot resolve module: mcp_lib.lazy_registry
error: test-runner: spec executed nothing (unresolved-module)
Results: 1 total, 0 passed, 1 failed
```

Verified pre-existing: the file was not edited by the sspec-modernization
session; the failure reproduces on the untouched tree (2026-08-26,
`bin/simple test test/01_unit/lib/mcp/lazy_loading_spec.spl`).

## Cause
The spec imports `mcp_lib.lazy_registry` and `mcp_lib.category_loaders`
(`init_registry`, `register_handler_metadata`, `call_cached_handler`, ...).
No `mcp_lib` tree exists anywhere under `src/lib/` —
`grep -r lazy_registry src/lib/` returns nothing. The MCP server code now
lives under `src/lib/nogc_sync_mut/mcp/` with a different module surface; the
lazy-registry / category-loader API this spec exercises was removed or
renamed without the spec following.

## Disposition
Left RED (correctly documents a broken import). Two options for the owner:
1. Re-point the spec at the current MCP module surface and re-express the
   lazy-loading contract there, or
2. Delete the spec if the lazy-registry design was abandoned.

Delete-candidate note: this was flagged as a delete-candidate in the
2026-08-26 sspec ORA batch because its import targets no longer exist.

## Unblock condition
Restore or re-home the lazy registry/category loader API, or rewrite the spec
against `src/lib/nogc_sync_mut/mcp/**`; the spec must reach
`Results: N total, N passed, 0 failed`.
