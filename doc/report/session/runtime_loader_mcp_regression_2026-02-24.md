# Runtime Regression Update (2026-02-24)

## Scope

Stabilize runtime behavior for:
- Loader ownership/unload in compatibility loader path
- MCP debug-log JSON tree response over stdio server path

## Code Paths Updated

- `src/compiler/99.loader/module_loader.spl`
- `src/compiler/99.loader/jit_instantiator.spl`
- `src/app/mcp/main_lazy.spl`

## SSpec Additions

### 1) Loader ownership fallback unload

File: `test/unit/compiler/loader/module_loader_spec.spl`

Added example:
- `purges __jit__ cache entries that match owner path tag`

Intent:
- Verifies module reload/unload removes JIT cache/global entries when owner metadata is `__jit__` and symbol naming matches module path tag.
- Verifies unrelated JIT symbols remain cached and registered.

Verification:
```bash
SIMPLE_LIB=src bin/simple test test/unit/compiler/loader/module_loader_spec.spl --mode=interpreter
# Result: PASS (68 passed)
```

### 2) MCP stdio runtime contract (stable wrapper path)

File: `test/integration/app/mcp_stdio_integration_spec.spl`

Added example:
- `MCP Protocol Runtime / returns tool-level isError for unknown tool`

Intent:
- Exercises framed stdio transport against `bin/simple_mcp_server`.
- Verifies unknown tool responses use tool-level MCP error payload (`isError: true`) instead of top-level JSON-RPC `error`.

### 3) MCP stdio debug tree JSON path

File: `test/integration/app/mcp_debug_log_tree_stdio_spec.spl`

Added example:
- `MCP Stdio Debug Log Tree / returns JSON tree and keeps session alive`

Intent:
- Exercises `tools/call` for `debug_log_enable` and `debug_log_tree(format=json)` over real stdio framing.
- Asserts response id, json format marker, and tree payload marker.

## Documentation Updates

File updated:
- `doc/guide/HOW_TO_USE_MCP.md`

Changes:
- Replaced outdated claim that terminal stdio testing is expected to timeout.
- Added framed-terminal testing guidance with two regression commands:
  - `mcp_stdio_integration_spec.spl` (runtime contract)
  - `mcp_debug_log_tree_stdio_spec.spl` (debug tree JSON path)

## Notes

- In this environment, interpreter startup logs are noisy due unrelated export warnings, but both stdio integration specs above now complete and pass reliably via `bin/simple_mcp_server`.
