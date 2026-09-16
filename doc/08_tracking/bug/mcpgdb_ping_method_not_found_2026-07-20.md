# `mcpgdb` app MCP server: `ping` now returns JSON-RPC "Method not found" instead of empty result

**Date:** 2026-07-20
**Component:** `src/app/mcpgdb/main.spl` MCP JSON-RPC dispatch
**Severity:** Low — single isolated example; 5 of 6 examples in the same
spec file pass
**Found by:** whole-suite triage campaign,
`test/02_integration/app/mcpgdb_log_modes_spec.spl`

## Symptom

```simple
it "preserves normal MCP ping handling":
    val (out, err, code) = _ping_mcpgdb()
    expect(code).to_equal(0)
    expect(out).to_contain("\"jsonrpc\":\"2.0\"")
    expect(out).to_contain("\"result\":{}")
```

fails at the `"result":{}` check. Actual `out`:

```json
{"jsonrpc":"2.0","id":"1","error":{"code":-32601,"message":"Method not found"}}
```

i.e. the `mcpgdb` MCP server no longer recognizes `ping` as a valid method
and returns a JSON-RPC `-32601 Method not found` error instead of the
expected empty-result success response.

## Root-cause hypothesis

Not root-caused to the exact dispatch table in `src/app/mcpgdb/main.spl`
(time-boxed triage). Either `ping` handling was dropped/renamed during a
refactor of the MCP dispatch table, or this server never wired up `ping`
and the spec's expectation predates the current dispatch implementation.
Worth checking against sibling MCP apps (e.g. `app_mcp_intensive_spec.spl`,
which does have a working `ping` health-check flow) for whether `ping`
support is supposed to be a shared/standard MCP surface across all these
CLI-embedded MCP servers.

## Note

Spec left unmodified — could not confirm from source whether dropping
`ping` support was intentional; flagging as a genuine gap rather than
guessing at a test-side fix.
