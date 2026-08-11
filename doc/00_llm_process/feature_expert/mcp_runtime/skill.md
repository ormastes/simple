# Feature Expert: MCP Runtime Verification

## Scope

Own the Simple MCP and Simple LSP MCP production-wrapper verification path:
`src/app/mcp/`, `src/app/simple_lsp_mcp/`, `bin/simple_mcp_server`,
`bin/simple_lsp_mcp_server`, the stdio integration spec, and the native smoke.

## Canonical evidence

```bash
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/check/check-mcp-native-smoke.shs
```

Require an executed scenario verdict; wrapper-contract markers alone do not
prove the servers. Native smoke also requires admitted, hash-bound MCP and LSP
artifacts under `bin/release/<triple>/`.

## Interpreter performance boundary

Explicit `CompileMode.Interpret` entries must not bulk-load all of `src/app`,
`src/lib`, `src/compiler`, and `src/runtime`. Imports are resolved lazily by
`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`.
The owner condition is in
`src/compiler/80.driver/driver_source_pipeline_loading.spl`. A regression
usually appears as 600+ source warnings, multi-gigabyte RSS, and CPU-guard
termination before the first scenario.

Current deployment caveat and resume evidence:
`doc/08_tracking/bug/mcp_stdio_interpreter_gate_exceeds_cpu_guard_2026-08-10.md`.

## Runtime-symbol boundary

MCP app code must use Simple facades. If JIT reports an unresolved `rt_*`
symbol, first prove the Simple facade, interpreter extern, and native runtime
implementation exist. Only then repair the central JIT runtime provider; never
add an MCP-local extern or accept interpreter fallback as native performance.
