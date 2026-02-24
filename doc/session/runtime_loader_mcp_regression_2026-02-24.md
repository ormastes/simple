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

### 2) MCP stdio debug tree JSON path

File: `test/integration/app/mcp_stdio_integration_spec.spl`

Added helper:
- `tools_call_request(id, name, arguments_json)`

Added example:
- `MCP Stdio E2E - Debug Log Tree / returns JSON tree without dropping stdio session`

Intent:
- Exercises `tools/call` for `debug_log_enable` and `debug_log_tree(format=json)` over real stdio framing.
- Asserts response id, json format marker, and tree array payload marker.

## Documentation Update

File updated:
- `doc/guide/HOW_TO_USE_MCP.md`

Changes:
- Replaced outdated claim that terminal stdio testing is expected to timeout.
- Added framed-terminal testing guidance and a direct integration-spec command.

## Notes

- In this environment, the full `mcp_stdio_integration_spec.spl` run is noisy/slow due broad module loading and warning spam, so end-to-end runtime probing was also verified directly against `bin/simple_mcp_server` with initialize + debug tools calls.
