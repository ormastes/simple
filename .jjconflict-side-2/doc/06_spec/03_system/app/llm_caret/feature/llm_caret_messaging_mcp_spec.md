# LLM Caret Messaging MCP

This manual verifies the dedicated `caret messaging mcp` server rather than
the SPipe documentation MCP.

## Operator flow

1. Start the compiled Caret artifact with `caret messaging mcp`.
2. Send MCP `initialize`, then `tools/list`.
3. Confirm all twelve `chat_*` tools have operation-specific object input
   schemas with unknown properties rejected.
4. Call `chat_open_private` with workspace, caller, target, canonical room ID,
   stable idempotency key, and timestamp.
5. Call `chat_send`, then `chat_read` for that direct room.
6. Confirm evidence changes from `primitive_direct_room` to `accepted` and
   `canonical_history`, with one canonical message.
7. Attempt to override the process-bound identity/workspace in tool arguments
   and confirm `workspace_access_denied`.

The MCP process reads its canonical identity, workspace, scopes, and durable
PureDatabase path from launch configuration. Tool arguments may narrow or echo
that authority but cannot replace it.

## Evidence boundary

This proves MCP SDK registration and canonical in-process dispatch through the
pure-Simple database. It does not claim credential-backed external-platform
delivery. Interpreter-hosted diagnostics exercise app-local stdio framing;
production uses the cached Caret and database SMF/native artifacts.

## Source

`test/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.spl`
