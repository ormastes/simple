# Secure Pure-Simple database server

Source: `test/03_system/database/server/secure_pure_simple_db_server_spec.spl`

## Primary operator flow

1. **Authenticate the database principal.** Missing, wrong, and unknown
   credentials receive the same `auth` denial; the configured credential opens
   exactly one capability-bound session.
2. **Shut down and release the connection.** EOF closes every session opened
   by that connection and discards its uncommitted overlay; production capacity
   is one authoritative connection owner.
3. **Bound a batch or range response.** A transaction reads its pending writes
   in deterministic key order, while oversized input is rejected before any
   batch item is queued.

## Supporting durability scenarios

The existing mirrored durability spec proves restart-persisted row versions,
durable commit receipts, reconnect retry without reapplication, and rejection
when one commit identifier is reused for different transaction content.

## Verification status

The scenario source contains no stubs. Runtime execution and generated-doc
regeneration remain blocked until a healthy admitted Stage-4 Pure-Simple CLI is
available; this manual is not credited as generated evidence before that gate.
