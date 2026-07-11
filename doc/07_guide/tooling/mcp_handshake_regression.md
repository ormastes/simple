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
