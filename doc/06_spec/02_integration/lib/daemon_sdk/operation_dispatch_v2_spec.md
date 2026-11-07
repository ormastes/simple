# Retained operation outcomes and response delivery

**NOT_RUN.** Authored manual, not generated runtime evidence. Source:
`test/02_integration/lib/daemon_sdk/operation_dispatch_v2_spec.spl`.

Open a private real operation journal and admit an immutable request. A duplicate
must return retained admission without another commit; the same ID with changed
payload must reject. Begin must publish execution intent once. Completion before
execution intent and a repeated begin must reject.

Persist result bytes and record their terminal digest. Inject response publication
failure: the acknowledgement callback must never run and the terminal journal
record must remain intact. Close/reopen the journal and publish the retained
bytes into a real response file, then acknowledge the corresponding request.
The reopened operation must not allow a second execution.

Inject acknowledgement failure after successful response publication. The response
file and terminal outcome must remain available. Reject changed result bytes,
changed request identity, nonterminal response publication and contradictory
terminal results before callbacks can disclose or acknowledge anything.

Finally, recover an executing operation into outcome-unknown. A subsequent begin
must refuse, preserving uncertainty instead of reissuing an effect.

These tests exercise an internal owner port. They do not certify caller
authentication, domain authorization, power-loss durability or a deployed daemon.
