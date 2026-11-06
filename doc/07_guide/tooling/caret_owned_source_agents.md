# Owned agent processes for source sessions

Status: implemented source; runtime qualification **NOT_RUN**. This opt-in supports the authenticated source-session host; legacy provider launches retain their existing behavior and do not gain source credentials.

`launch_multi_caret_manager(..., owned_source_sessions: true)` and the matching team/plan launch option use the existing provider plan arguments. The configured provider must be an absolute path; the canonical native executable owner pins it and validates its SHA-256 digest before launch. No shell or PATH fallback is added. The prompt remains in argv, stdin is closed empty, the process has a one-hour deadline, 250 ms termination grace, and at most 4 MiB captured per output stream. The supervisor must poll independently of incoming HTTP requests; this is not autonomous containment merely because a lease exists.

Each successful spawn obtains a cryptographically random owner identity and an opaque process lease. `pid=-1` is intentional: the native owner does not expose a PID. The manager and authenticated host use the same lease; PID existence is never source-session authority. Legacy process records and caller-shaped identity strings without a lease cannot authenticate an agent.

The parent retains the executable pin until process collection. Polling preserves owners on errors and keeps cleanup-pending teams degraded rather than terminal. Stop requests cancellation, polls for at most twenty 100 ms steps, and collects only a terminal/reaped child. Failed collection or pin close stays explicit and reachable for the next supervisor cleanup attempt. A failed identity admission cancels the already-started child; a later team launch failure rolls back all earlier owned children. These are source contracts, not retained platform acceptance receipts.

## Qualification

Build `test/fixture/source_view/managed_agent.spl` with an admitted native compiler, then set `SOURCE_SESSION_TEST_AGENT` to that absolute binary path when executing `test/01_unit/app/llm_caret/owned_agent_process_spec.spl` and the authenticated HTTP host specs. The fixture sleeps for 60 seconds and does not invoke a model, access the network, or write files. Missing fixture configuration fails instead of skipping. Run the parent manager/HTTP listener composition and independent heartbeat, cancellation, terminal collection, parent-death and provider failure checks before claiming live session integration.

The authored manual is not generated SPipe evidence. Other host providers, parent-death containment and runtime fault injection remain unqualified until the exact-runtime receipts exist.

Collection receipt repair (review cycle 2): reaped receipts consume the canonical
lease except runtime errors 11 and 16. Consumed errors remain errors after the
lease is dropped; pin close is attempted, and a failed close retains the pin and
both failure reasons. Retryable receipts retain ownership. Repeated stop preserves
settled collection errors. An accepted spawn receipt with a runtime error enters
cleanup before any identity is minted. Adjacent receipt controls exercise the
production transition and cleanup predicate; these synthetic receipts do not
establish native failure-injection coverage. All new controls remain **NOT_RUN**
until an admitted runtime is available.
