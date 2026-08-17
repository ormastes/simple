# MCP `debug_log_tree` tool call produces no matching response for either JSON or LLM-text mode

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-07-20
**Component:** MCP stdio server `debug_log_tree`/`debug_log_enable` tool
handlers (source not isolated in this pass — reachable via
`test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl`'s stdio session)
**Severity:** Medium — both examples in the file fail (0 of 2 pass)
**Found by:** whole-suite triage campaign

## Symptom

```simple
it "returns JSON tree and keeps session alive":
    val input = init_request() + initialized_notification()
        + tools_call_request("2", "debug_log_enable", "{\"pattern\":\"*\"}")
        + tools_call_request("3", "debug_log_tree", "{\"format\":\"json\",\"mode\":\"human\"}")
        + shutdown_request("4")
    val output = send_mcp(input)
    expect(output.contains("\"id\":\"3\"")).to_equal(true)   # FAILS
    ...
```

Both examples (`json`/`human` mode and `text`/`llm` mode) fail at the very
first check — the response for request id `"3"` (the `debug_log_tree` call)
is not present in the session's combined output at all. Session shutdown
(id `"4"`) presumably also isn't reached correctly since neither example
gets past its first `expect`.

## Root-cause hypothesis

Not root-coded to the exact handler (time-boxed triage — the MCP stdio
server implementation wasn't traced through in this pass). Either
`debug_log_enable` (called first, id `"2"`) fails/hangs the session before
`debug_log_tree` can be dispatched, or `debug_log_tree` itself isn't wired
into the tool dispatch table under this server.

## Note

Spec left unmodified — no evidence found that the tool names/params are
stale; flagged as a genuine gap for someone with more context on the debug
MCP stdio handler to investigate.

## Re-verification 2026-08-17 (app-rest lane) — dispatch hypothesis REFUTED; behaviour UNVERIFIED

This doc's "not wired into the dispatch table" hypothesis is wrong. Both tools
are wired in current source:
- `src/app/mcp/main_dispatch.spl:271` `if name == "debug_log_enable":`
- `src/app/mcp/main_dispatch.spl:279` `if name == "debug_log_tree":`
- handlers at `src/app/mcp/debug_log_tools.spl:148` and `:228`
- schemas at `debug_log_tools.spl:26` and `:102`
- registry entry in `src/app/mcp/tool_table.spl:459`

Whether the id-`"3"` response is actually emitted still needs the stdio session
spec, which was not run in this lane. Verdict: root-cause hypothesis refuted;
symptom UNVERIFIED.
