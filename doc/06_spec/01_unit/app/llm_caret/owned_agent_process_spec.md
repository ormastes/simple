# Owned source-agent process acceptance

Status: **AUTHORED / NOT_RUN**. No admitted Simple runtime or generated-manual receipt is asserted.

The executable spec is `test/01_unit/app/llm_caret/owned_agent_process_spec.spl`.

1. Reject missing/relative providers, too many arguments and embedded NUL before spawn.
2. Reject caller-shaped identity/PID metadata without an opaque process lease.
3. Start the controlled native fixture with the real provider-plan path, observe a live lease, then cancel/collect and close the pin.
4. Roll back an earlier live owned child when a later provider is invalid.
5. Publish distinct manager-owned spawn identities, then stop every child and reject stale lease liveness.
6. Preserve ordinary callers without granting source authority.

Prerequisite: an admitted native build of `test/fixture/source_view/managed_agent.spl` supplied through `SOURCE_SESSION_TEST_AGENT`. A missing prerequisite fails. The fixture is finite and has no external provider/network behavior. Production failure injection, parent-death and cross-host lifecycle qualification remain open.

Collection receipt repair (review cycle 2): reaped receipts consume the canonical
lease except runtime errors 11 and 16. Consumed errors remain errors after the
lease is dropped; pin close is attempted, and a failed close retains the pin and
both failure reasons. Retryable receipts retain ownership. Repeated stop preserves
settled collection errors. An accepted spawn receipt with a runtime error enters
cleanup before any identity is minted. Adjacent receipt controls exercise the
production transition and cleanup predicate; these synthetic receipts do not
establish native failure-injection coverage. All new controls remain **NOT_RUN**
until an admitted runtime is available.
