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

A static author scan found no placeholder stubs in the scenario source; no
maintained-manual scorecard is claimed. Runtime execution and generated-doc
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

### Temporary staged-binary diagnostics (2026-08-14)

These are diagnostics only, not admitted Stage-4 or release evidence.

- The retained in-lane Stage-2 artifact and producer transcript are identified
  in `doc/09_report/secure_pure_simple_servers_evidence_status.md`; an
  unverified operator observation says its `check` and `test` probes returned
  `unknown command`. External sibling candidates are intentionally not used as
  reproducible evidence.
- Unverified operator observations from the authorized Rust-seed fallback
  `src/compiler_rust/target/bootstrap/simple`, SHA-256
  `c9321d38fa7623008e185289bc9dc193489ab490f7ec238b9a3cadcd0b4788ea`,
  version `Simple Language v1.0.0-beta`: durability was 22/0. After bounded
  test-only fixes, secure server was 7/0 and tier server ended 39/1; the one
  remaining RED is UTF-8 batch round-trip (`猫` became replacement characters).
  The tier reached its three-attempt cap. These observations have no retained
  immutable command transcript and therefore receive no acceptance credit;
  the symptom is unresolved and not attributable between seed/runtime and the
  server implementation.
- An unverified operator observation of the one Stage-2 native-build attempt
  says it reached link and failed on
  missing `core-c-bootstrap` symbols `rt_file_create_excl`, `rt_file_sync`, and
  `rt_crc32_text`; no executable was produced and no command variant was retried.
