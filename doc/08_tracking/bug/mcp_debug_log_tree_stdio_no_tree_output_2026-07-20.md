# MCP `debug_log_tree` tool call produces no matching response for either JSON or LLM-text mode

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Older than 45 days; has a concrete spec (`test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl`) but was not re-run in this pass. Closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
