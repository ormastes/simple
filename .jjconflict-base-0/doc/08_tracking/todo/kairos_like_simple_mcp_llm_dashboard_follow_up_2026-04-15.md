# KAIROS-Like Simple MCP + Dashboard Follow-Up

Date: 2026-04-15

## Status

This is a follow-up TODO, not a new bug.

The current assistant-core slice is working:

- `assistant_start` returns a correct MCP result again
- MCP-created sessions are persisted through `src/app/mcp/assistant/**`
- `bin/simple dashboard assistant` replays those sessions successfully
- the assistant-core store/query specs and the MCP/dashboard end-to-end spec pass

## Remaining Work

1. Move the remaining assistant lifecycle handlers onto the extracted core API instead of keeping partial lifecycle logic in `src/app/mcp/main_lazy_assistant.spl`.
2. Route child-task creation and task-tree state through `src/app/mcp/assistant/session_store.spl` so parent/child relationships are first-class core records.
3. Rewire `assistant_list_tasks` to use structured core task state rather than session-only projections plus dashboard task side-loading.
4. Continue the dashboard live-bridge/session-tree integration on top of the extracted assistant core.
5. Add focused regressions for pause/resume/push-signal/task-tree behavior after the remaining handlers are moved.

## Not A Bug

Do not track this as a language/runtime bug:

- generic `n as i64`
- generic `"{n as i64}"`
- assistant session replay visibility

Those paths are already verified in the current tree.

## Next Slice

Recommended next implementation slice:

1. child-task core extraction
2. MCP handler migration for spawn/list task paths
3. dashboard task-tree view tightening against the extracted core records
