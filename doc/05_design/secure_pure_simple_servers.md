<!-- codex-design -->
# Secure Pure-Simple Servers Detail Design

## Interfaces

- `SecureServerPolicy`: immutable web limits, timeout/read budgets, TLS-required
  flag, and explicit plaintext-development constructor.
- `DbListener` / `TcpDbListener`: concrete listener port and production owner;
  `DbServerCapsule.listen/stop_listening` composes lifecycle and capacity.
- `DbTransport`: bounded framed `read`, bounded `write`, idempotent `close`.
- `TcpDbTransport`: concrete production adapter implementing `DbTransport`.
- `AuthenticatedPrincipal`: non-secret principal identity produced only by the
  credential verifier; capability lookup accepts this type, not claimed text.
- `CommitIdentity`: validated bounded ID and authenticated principal; durable
  receipts additionally retain the exact transaction fingerprint.
- `BoundedQuery`: item, encoded-response-byte, and scan-work limits used by
  batch/range handlers.

## Web flow (REQ-001..003)

1. Validate `SecureServerPolicy`; production requires TLS and valid material.
2. Bind through the owned TCP facade and account the accepted connection.
3. Production: wrap the stream in an owned encrypted adapter. Until GAP-TLS-3
   is implemented, return unavailable and close; never pass bytes as plaintext.
4. Read with line/header/body/iteration/timeout limits. Reject ambiguous
   framing, duplicate security-sensitive headers, unsupported coding, or
   traversal before constructing a routed request.
5. Attach request identity, route once, apply security headers, write a bounded
   response, then close at the keep-alive bound and release accounting.

## DB flow (REQ-004..008)

The accept loop reserves a connection slot before spawning/serving, constructs
one session, and guarantees `transport.close`, session rollback/removal, and
slot release for EOF, parse failure, authentication failure, handler failure,
and shutdown. Every frame is bounded before decoding.

`OPEN` parses bounded principal and credential fields. The verifier performs a
fixed-work comparison across the configured credential width and returns the
same unauthorized response for missing principal, missing credential, unknown
principal, and mismatch. Diagnostics contain only the rejection category.
Capability lookup occurs only with `AuthenticatedPrincipal`.

All store reads and mutations enter the authoritative store owner. Commit holds
that boundary from optimistic precheck through in-memory apply, durable atomic
save, row-version/commit-record persistence, and response outcome creation.
Failure restores the prior in-memory state before releasing the boundary.

On `COMMIT commit_id=<validated text>`, lookup precedes apply. A matching durable
fingerprint returns its recorded applied count; a different fingerprint using
the same ID conflicts. This record and row versions reopen with the database.

Batch writes first validate shape, item count, bytes, capabilities, and all
conflict expectations, then add the complete batch to the transaction overlay.
Range reads merge committed rows with the caller's overlay, filter by endpoints,
sort by stable key, and stop before exceeding item or response-byte limits.
Overflow returns one error and publishes no partial response or mutation.
The production `serve_tcp` and scripted adapters both route through
`bounded_message_response`; runtime TCP proof remains required.

## Errors and shutdown

Errors are data, not panics: invalid policy, unavailable TLS, bad frame,
unauthorized, forbidden, conflict, capacity, persistence, response-too-large,
and shutdown. Shutdown stops new accepts, closes the listener, drains or closes
bounded active transports, rolls back open overlays, and reaches zero slots.

## SSpec/manual contract

Primary operator steps are exactly:

1. `Bind the production listener`
2. `Reject an unsafe web request before dispatch`
3. `Authenticate the database principal`
4. `Commit and recover one durable transaction`
5. `Retry one commit id without reapplying`
6. `Bound a batch or range response`
7. `Shut down and release the connection`

Fixture/checker names are `secure_web_server_fixture`,
`secure_db_server_fixture`, `expect_web_request_rejected`,
`expect_db_auth_rejected`, `expect_commit_recovery`, and
`expect_bounded_query`. Any unavailable helper must fail explicitly.

## Verification notes

Use independent observations: loopback client responses, router invocation
count, bind-after-shutdown, a peer reader, reopened database files, and exact
ordered payloads. Configuration-only TLS checks are partial evidence and must
leave REQ-003 blocked until encrypted application bytes traverse GAP-TLS-3.
