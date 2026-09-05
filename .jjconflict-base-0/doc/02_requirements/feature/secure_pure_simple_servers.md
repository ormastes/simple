<!-- codex-design -->
# Secure Pure-Simple Servers — Feature Requirements

Status: Accepted (selected in `.spipe/secure_pure_simple_servers/state.md`)

## Scope

The canonical Pure-Simple web and database server paths must fail closed at
their network, authentication, authorization, transaction, and persistence
boundaries. Owned socket/file capability providers are allowed; foreign
protocol servers, raw-source production wrappers, and new leaf `rt_*`
declarations are excluded.

## Requirements

- **REQ-001 (AC-1):** A real TCP connection entering the canonical web
  entrypoint traverses the hardened parser, router, response writer, security
  headers, and request-identity path.
- **REQ-002 (AC-2):** Web handling bounds request-line size, header count and
  line size, body size, read iterations, keep-alive lifetime, and timeout, and
  rejects malformed or ambiguous framing, conflicting duplicate security
  headers, unsupported transfer coding, and static-file traversal before
  dispatch.
- **REQ-003 (AC-3):** Production startup rejects missing or invalid
  certificate/key material and never downgrades to plaintext. Plaintext
  development operation is an explicit policy choice.
- **REQ-004 (AC-4):** The DB server owns a bounded `DbListener` accept
  lifecycle, a `DbTransport` per connection, cleanup on every exit, explicit
  shutdown, and bounded message and connection capacity.
- **REQ-005 (AC-5):** `OPEN` authenticates an `AuthenticatedPrincipal` before
  capability lookup. Missing, unknown, and wrong credentials are
  indistinguishable externally; secrets are neither logged nor echoed; secret
  comparison has no content-mismatch early exit.
- **REQ-006 (AC-6):** One authoritative mutation owner or explicit
  synchronization boundary serializes shared DB state, and readers cannot
  observe the in-memory P3/P4 durability window.
- **REQ-007 (AC-7):** Durable row conflict tokens survive reopen, and a
  client-supplied `CommitIdentity` makes retry/reconnect idempotent, including
  a lost commit acknowledgement.
- **REQ-008 (AC-8):** `BoundedQuery` batch/range operations retain per-table
  capability checks, transaction-overlay semantics, deterministic ordering,
  and response-size bounds; overflow causes no partial application.
- **REQ-009 (AC-9):** Executable SSpec scenarios provide absolute oracles for
  real web routing/rejection, DB authentication and cleanup, concurrent
  visibility, restart conflict, idempotent retry, and bounded batch/range, with
  deliberate-red calibration and REQ/AC traceability.
- **REQ-010 (AC-10):** Every changed SSpec has one maintenance scorecard and a
  mirrored `doc/06_spec` manual with zero stubs; executable specs exist only
  below `test/` and primary flows use the accepted shared step vocabulary.
- **REQ-011 (AC-11):** The canonical Phase-6 plan, requirements/design links,
  Pure-Simple server guide, expert skills, and unresolved bug records describe
  current behavior and blockers. SPipe workflow/command changes are N/A.
- **REQ-012 (AC-12):** Changed Simple files pass focused check/lint/test,
  duplication, dependency, numbered-artifact, direct-runtime, STUB001, and
  spec-layout gates. The whole interpreter suite is required after a healthy
  Stage-4 self-hosted CLI is admitted.
- **REQ-013 (AC-13):** A fresh highest-capability reviewer accepts scope,
  interfaces, security/durability semantics, manual quality, exclusions,
  evidence, and done marks.
- **REQ-014 (AC-14):** Intentional changes are committed and integrated under
  `/tmp/simple-main-restart12-push.lock`: fetch, rebase on `origin/main`, push
  `HEAD:main` with GitHub token environment variables unset, refetch, prove
  reachability, and leave a clean detached worktree without force or a branch.

## Known blocker

REQ-003 is not complete merely because certificate validation fails closed.
`tls_server.spl` records GAP-TLS-3: there is no native encrypted-stream overlay
from `TcpStream`. Production TLS acceptance therefore remains blocked until an
owned encrypted stream completes a handshake and carries HTTP bytes; plaintext
development mode is not substitute evidence.
