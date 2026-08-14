# Secure Pure-Simple servers: evidence status

Date: 2026-08-14

## Authored, statically reviewable evidence

- `secure_pure_simple_db_server_spec.spl` calls the production `listen` entry
  point only for deterministic pre-bind rejection of zero connection capacity,
  then asserts listener/connection state remains released.
- `db_durability_spec.spl` covers the P3/P4 crash boundary and a reconnect retry
  using a durable, principal-bound commit receipt. Cross-principal and
  different-content reuse are explicit conflicts.
- DB capability coverage includes read-only, empty-grant, wrong-table,
  missing-table, write-only, and data-operation denial cases.
- Missing, wrong, and unknown credentials are checked against one exact
  `ERR code=auth msg=authentication failed` frame.
- The tier spec source contains an injected isolation violation plus
  unconditional controls, so static review finds a non-placeholder oracle;
  deliberate-red execution remains uncredited.
- Mirrored manuals exist for all three DB system specs.

## Release-blocking evidence not available

The deployed Pure-Simple Stage-4 CLI is unhealthy. Consequently this lane did
not execute the listener scenario, DB specs, `sspec-maintain scan`, or
`spipe-docgen`; it did not produce a genuine deliberate-red failure/restoration
transcript, runtime coverage, socket transcript, or `0 stubs` generator
receipt. Hand-authored manuals are not represented as generated provenance.

A live listener PASS is intentionally absent. A trustworthy scenario needs a
concurrent client/stop fixture that binds an assigned loopback port, connects,
exchanges messages, closes, and joins the listener owner. Calling `listen` with
no connector can hang when accept polls for shutdown; accepting any bind error
would be a vacuous oracle. Until that fixture and the runtime are admitted, the
real bind/accept/EOF/stop row is RED/BLOCKED, not skipped or passed.

Production and scripted drains now share `bounded_message_response`, and the
focused source scenario constructs an oversized encoded result. Runtime TCP
wire evidence remains RED/BLOCKED; structural sharing is not a socket transcript.

AC-9, AC-10, AC-12, and final-review AC-13 remain open. Production TLS remains
separately blocked by GAP-TLS-3. Static source shape cannot prove actual socket
accept/cleanup, scheduler exclusion across P3/P4, fsync/rename crash behavior,
or lost-ack replay behavior; those require the healthy admitted runtime.
