# `mcpgdb` app MCP server: `ping` now returns JSON-RPC "Method not found" instead of empty result
## Resolved 2026-11-25

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

## Resolution 2026-11-25

**Status:** resolved. The dispatch gap was already fixed on this branch;
unrelated compile errors in the mcpgdb app (which masked end-to-end
verification) were fixed in the same change.

### Findings

1. **Ping dispatch is present and correct.** `mcpgdb` delegates JSON-RPC to
   `mcp_serve` from `std.mcp_sdk.server.app`
   (`src/app/mcpgdb/main.spl:11`), which resolves to the
   `nogc_sync_mut` facade. `mcp_server_handle` handles `ping` explicitly:
   `src/lib/nogc_sync_mut/mcp_sdk/server/app.spl:221-222` returns
   `jsonrpc_result(id, "{}")` for `has_method(msg, "ping")`. The
   router variant agrees (`src/lib/nogc_sync_mut/mcp_sdk/server/router.spl:45,128`).

2. **Direct execution evidence.** A minimal server using the same facade
   (`mcp_server_init` + `StdioTransport.json_lines()` + `mcp_serve`),
   fed `{"jsonrpc":"2.0","id":"1","method":"ping"}` on stdin, answers:

   ```json
   {"jsonrpc":"2.0","id":"1","result":{}}
   ```

   No `-32601`. Command (worktree root, tracked `bin/simple.exe`):
   `printf '{"jsonrpc":"2.0","id":"1","method":"ping"}\n' | SIMPLE_LIB=src bin/simple.exe run <probe>.spl`

3. **Compile errors masked verification.** On this branch the mcpgdb app
   did not compile at all, so every CLI invocation exited 1 (4 spec
   examples failed on `expected 1 to equal 0`). Two sites matched the
   outdated Option-style API (`Some(i)` / `nil` patterns) on functions
   that now return `i64` (`src/lib/text.spl:74`
   `last_index_of -> i64`, `index_of -> i64`), producing
   `error[SPL-PAT-001]`:
   - `strip_prompt` in `src/app/mcpgdb/debug_backend_common.spl` and
     `src/app/mcpgdb/backend_common.spl` (`last_index_of`)
   - `find_lsp_message_for_id` in `src/app/mcpgdb/backend_common.spl`
     (`index_of`)

   Fixed by binding the `i64` index directly and guarding with
   `if idx >= 0:` / `if idx < 0: return ""`.

### Verification

`SIMPLE_LIB=src bin/simple.exe test test/02_integration/app/mcpgdb_log_modes_spec.spl --mode=interpreter`
on Windows (tracked worktree `bin/simple.exe`):

```
6 examples, 0 failures
SPEC FILE VERDICT: test/02_integration/app/mcpgdb_log_modes_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 blocked=0 dropped=0
Results: 6 total, 6 passed, 0 failed, 1 skipped
```

The ping example reports an honest skip on this host
(`mcpgdb_bundle_validate_v1` fails without the admitted native tool
bundle on Windows, and the spec skips rather than false-passes); the
runner still counts it green and the ping dispatch itself is verified by
finding 2 above. The other five examples (help, json ready, dot
progress, invalid log mode, json unknown option) pass for real.

### Files changed

- `src/app/mcpgdb/backend_common.spl` — `strip_prompt` i64 fix
- `src/app/mcpgdb/debug_backend_common.spl` — `strip_prompt` i64 fix
- `doc/08_tracking/bug/mcpgdb_ping_method_not_found_2026-07-20.md` — this section

