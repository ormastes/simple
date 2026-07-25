# MCP Handshake Regression Gate

The production `bin/simple_mcp_server` wrapper has two startup paths:

- default core handshake: `SIMPLE_MCP_FULL=0`
- full Simple server: `SIMPLE_MCP_FULL=1`

Both paths must preserve supported JSON-RPC integer and string request IDs.
Numeric IDs remain JSON numbers and string IDs remain JSON strings. A response
ID of `null`, or selection of a nested `params.id`, is a correlation failure.

Run the integration gate with:

```sh
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
```

Run the packaged/native smoke with:

```sh
sh scripts/check/check-mcp-native-smoke.shs
```

Do not validate only with `SIMPLE_MCP_FULL=1`: that bypasses the default shell
handshake and previously allowed its ID parser to regress unnoticed.
`check-mcp-wrapper-contract.shs` extracts the generated wrapper from tracked
`setup.shs` into a temporary directory, so a stale `bin/` wrapper cannot mask a
source regression.

## Fresh bootstrap artifacts

Every bootstrap route that reaches the full server-producing Stage 5 removes
both MCP destinations before building, then runs this same native smoke once
against the exact fresh `simple_mcp_server` and
`simple_lsp_mcp_server` paths before deploy. The probe disables source fallback,
sends only the exact string request IDs expected by the validator,
sends `initialize`, `notifications/initialized`, and `tools/list`, then requires
successful `simple_status` and `lsp_symbols` calls with correlated response IDs
and semantic results. A missing or stale output, nonzero build or process exit,
timeout, malformed frame, JSON-RPC error, or MCP `isError` result fails the
bootstrap. Both native builds use `SIMPLE_NO_STUB_FALLBACK=1`. Stages 2 and 3
run their own compiler/native fixture sanity and do not claim full-pair MCP/LSP
health; the separate Stage 2 MCP system spec covers its single cached MCP
artifact. `--no-mcp` likewise makes no Stage 5 MCP/LSP health claim.
