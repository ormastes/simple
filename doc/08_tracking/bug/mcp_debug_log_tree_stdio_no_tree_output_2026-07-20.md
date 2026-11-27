# MCP `debug_log_tree` tool call produces no matching response for either JSON or LLM-text mode
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Triage 2026-11-25 (P2 ledger sweep, Windows worktree)

The "isn't wired into the tool dispatch table" half of the hypothesis is
disproven by inspection at this HEAD: `debug_log_tree` is registered in the
tool table (`src/app/mcp/tool_table.spl:460`), mapped in the CLI-passthrough
dispatch (`src/app/mcp/main_dispatch.spl:292` -> `("log tree", 10)`), handled
by `handle_debug_log_tree` (`src/app/mcp/debug_log_tools.spl:228`), and its
`format` argument is forwarded in `src/app/mcp/cli_passthrough.spl:375`.

The end-to-end stdio re-run is BLOCKED at this HEAD: `src/app/mcp/main.spl`
itself carries `@representation_boundary` (added repo-wide by `cfd89933699`),
which the pinned tracked seed (`bin/simple.exe`, Rust v1.0.0-rc.1) rejects,
so `bin/simple.exe run src/app/mcp/main.spl --mode=interpreter` — the exact
command the spec shells out to — fails at module load
(`unknown decorator '@representation_boundary'`) before the session starts.
Whether the response for id `"3"` is now emitted therefore remains
unverified at runtime. Status stays OPEN pending a re-run once the tracked
seed accepts the decorator (or a self-hosted binary is deployed); no source
change made by this sweep.

