# LLM Caret Primitive HTTP Application

This executable manual exercises the server-independent request dispatcher
used by the primitive HTTP/SSE listener.

## Covered flow

1. Authenticate a workspace-scoped room owner.
2. Create a canonical public room with an idempotency key.
3. Create a Claude agent profile and bind it to the room through the
   provider-neutral agent-control boundary.
4. Send a human message, observe `routed:true`, and retrieve the generated
   canonical task.
5. Send the message twice using one idempotency key and retain one sequence
   without waking the agent twice.
6. Read bounded history and advance a truthful `local_cursor` receipt.
7. Read the room event stream as `text/event-stream`.
8. Create a private direct room, close the PureDatabase runtime, and reopen it.
9. Confirm the persisted member can access the room while an outsider receives
   `room_access_denied`.

The TCP listener is a transport wrapper around this application boundary.
This evidence does not represent a live Slack, Teams, or other platform gate.
