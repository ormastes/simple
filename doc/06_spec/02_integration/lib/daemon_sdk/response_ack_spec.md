# Legacy daemon publication and acknowledgement failures

**NOT_RUN.** Authored manual, not generated runtime evidence. Source:
`test/02_integration/lib/daemon_sdk/response_ack_spec.spl`.

Create a private spool and an owned in-process runner. Publish a request whose
handler records an observable file effect. Place a directory at the final response
path to force real atomic publication failure. After one poll, the request must
remain, exactly one effect must exist and the runner must be publication-blocked.
A further poll must not invoke a handler.

Return a response bearing another request ID. The runner must reject it before
publishing a response or deleting the actual request. For a normal response,
confirm that the response file exists and the request is removed.

Simulate an acknowledgement race by removing the request during handling. After
successful response publication, the failed acknowledgement must stop polling
with an explicit acknowledgement-blocked state.

Each scenario releases only its own lock and temporary directory. These cases
do not claim V1 crash/restart idempotency; uncertain effects still require domain
reconciliation and the journal-backed V2 path before remote mutation is enabled.
