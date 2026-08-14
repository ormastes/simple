# Secure Pure-Simple database server

Source: `test/03_system/database/server/secure_pure_simple_db_server_spec.spl`

## Primary operator flow

1. **Authenticate the database principal.** Missing, wrong, and unknown
   credentials receive the exact same
   `ERR code=auth msg="authentication failed"` frame; the configured credential
   opens exactly one capability-bound session.
2. **Shut down and release the connection.** EOF closes every session opened
   by that connection and discards its uncommitted overlay; production capacity
   is one authoritative connection owner.
3. **Bound a batch or range response.** A transaction reads its pending writes
   in deterministic key order, while oversized input is rejected before any
   batch item is queued.

## Supporting durability scenarios

The existing mirrored durability spec authors checks for restart-persisted row
versions, durable commit receipts, reconnect retry without reapplication, and
rejection when one commit identifier is reused for different transaction
content. Those checks are not credited until execution.

## Verification status

The scenario source contains no stubs. Runtime execution and generated-doc
regeneration remain blocked until a healthy admitted Stage-4 Pure-Simple CLI is
available; this manual is not credited as generated evidence before that gate.
The deterministic listener scenario rejects zero connection capacity before
bind. A live bind/accept/client/EOF/stop lifecycle is deliberately not claimed:
it requires a concurrent client/stop fixture and an admitted runtime, and a
listener with no connector is not a bounded substitute.
Production `serve_tcp` and the scripted adapter now share
`bounded_message_response`. Static inspection and the focused authored scenario
cover the shared encoded limit; a runtime result remains uncredited.

Idle shutdown is owned by `DbListenerControl`: its mutex-backed
`DbStopControl` is shared with the external stop owner, and `request_stop()`
both publishes stop state and closes the listener so a blocked accept returns
and the address can be rebound. `DbTransport.write_message` returns success;
a failed reply terminates the drain, closes the transport, and closes every
session opened by that connection. The mirrored boundary specs exercise the
shared stop token and failed-write cleanup without claiming live TCP evidence.
