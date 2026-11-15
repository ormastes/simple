# MCP progressive hints feature expert

## Role

Owns the progressive-hint layer of the MCP server: the pure policy
`src/lib/common/llm/hint_policy.spl` (`decide_hint`) and its MCP wiring.
Plan: sections 7 and 9 (`HINT-001`..`HINT-010`) of the 2026-11-14 plan.

## Contract

- Tools `simple_help`, `simple_capabilities`, `simple_hint_status` live in
  `src/app/mcp/main_lazy_hint_tools.spl`; they are registered in
  `main_static_tools.spl` (tools/list, count 181), `tool_table.spl`
  (read-only schema) and routed by `main_dispatch.spl` (`_dispatch_ip_hint`).
- State: `main_session_state.spl` keeps one `HintState` per
  (`McpSessionId`, `HintCapability`). Sessions never share state. Request body
  field `session_id` selects the session (default `default`), `topic` the
  capability (`quickstart|testing|debug|traceability|skills`).
- `simple_capabilities(topic)` is a capability use: full, then brief, then
  quiet. `simple_help` is an explicit help request (always full).
  `simple_hint_status` only reads. Unknown topic is a tool error and stores
  nothing.
- The clock is read in the handler (`_hint_now`) and passed to `decide_hint`.
- Hint text names only tools from `hint_capability_tool_names`; the spec checks
  every name against the static manifest (`hint_missing_tools`), so a rename
  or removal fails `test/01_unit/app/mcp/mcp_hint_tools_spec.spl` (HINT-009).
- Perf: no file I/O on the request path; quiet responses touch only the
  in-memory slot list.

## Not done

See `doc/08_tracking/bug/mcp_progressive_hints_wiring_missing_2026-11-14.md`:
resources/prompts, hint appending in other tools' responses, ctx primitive_api,
HINT-010 CI gate, provider hooks.
