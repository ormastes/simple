# DaemonRunner publication and acknowledgement regressions

SSpec: NOT_RUN under an admitted compiler. Native diagnostic evidence, when
available, is separate and does not qualify the test runner or release.

Executable: `test/02_integration/lib/daemon_sdk/response_ack_spec.spl`.
Shared real-effect cases: `test/fixtures/daemon_sdk/publication_regression.spl`.

1. Handler writes an effect; a directory at the response path refuses atomic
   publication. Require unchanged original request bytes, one effect, blocked
   state, zero acknowledgements and no handler invocation on another poll.
2. Mismatched response ID must not publish or delete the original request.
3. Successful publication acknowledges the request; a subsequent poll has no work.
4. An externally removed request makes acknowledgement fail and stops dispatch.
5. With three requests in unspecified directory order, the first succeeds, the
   second refuses publication and the third stays untouched. Derive order from
   the handler's effects; only the successful prefix may be acknowledged.
6. Replace the request path with a nonempty directory during handling. Deletion
   refuses, the replacement entry and saved original bytes remain, the published
   response stays readable, and another poll cannot repeat effects. This proves
   retention of a replacement entry, not continued existence of the original file.
7. Reject request/response keys with newline/CR/equals and continuation lines that
   inject id, request_id, kind, status, timestamp or field headers. Check trimmed
   third-line prefixes. A real handler's injected response must retain the
   unchanged request and single effect without publishing an unreadable response.
8. At outer-loop cycle100, publication failure preserves blocked state and the
   old-response cleanup sentinel; the loop must return before cleanup/sleep.
9. A valid nonzero status is a response, not a transport failure: publish and
   acknowledge it. Ordinary legacy multiline output is accepted; its pre-existing
   truncation is not claimed fixed or lossless.

All fixtures use private roots and exact cleanup. V1 restart idempotency is not
claimed; uncertain effects still require domain reconciliation and the V2 journal.
This repair applies to DaemonRunner, not every application-specific daemon loop.
