# SDK errno worker observer

This observer collects missing failure-boundary evidence. It does not fix or
qualify the original SDK HIR failure. Production is explicitly disabled by
`SDK_ERRNO_OBSERVER_ENABLED_V1 = false`; an enabled diagnostic compiler requires
a separate immutable source revision and actual Hello proof.

The canonical HIR driver owner initializes a typed atomic budget before parser
leases. Initialization refuses a nonzero actual transient-scope state and uses
the checked process-ID facade. A failed allocation or PID query produces no
capture; absence is not success. HIR workers are separate processes. Within a
process emission shares the typed atomic budget; initialization remains a serial
driver operation and must not be called concurrently.

Canonical lowerer factories store three handoff scalars. The three actual
driver body-lowering calls refresh three body-entry scalars. No diagnostic
allocation or output occurs at these boundaries. The re-export root-return
hooks select the actual path ending `/nogc_sync_mut/io/path_identity.spl` and
exact requested symbol `path_errno_address` before reserving a slot. Unrelated
modules and symbols cannot consume the budget. The post-hop hook separately
records the existing projected terminal index/item without another resolver
walk. All original guard exits, memo mutations and diagnostics remain intact.

Each process emits at most eight records, each at most 2048 bytes including
escaping and the final LF. The common owner uses the existing stderr facade;
it does not claim durable publication. An external collector must retain raw
stderr, validate complete marked SDN, group records by actual positive PID,
reject interleaving/duplicate sequences or unavailable rows, and bind paths to
the exact source snapshot and producer/runtime receipts. The module-name field
is explicitly unavailable rather than invented. Both raw and normalized paths
are recorded. A partial capture does not establish worker equivalence.

The unit specification covers selected paths/symbols, concrete independent
handoff/body values, quoting, input/escaped-byte bounds and real typed atomic
reservation. The enabled native fixture verifies actual record count and
selection under an opted-in producer; it is a control, not a failing SDK build.
Only actual SDK worker records can explain the SDK failure. P2 is independent;
P3 remains skipped. Cycle usage is tracked in
`doc/03_plan/agent_tasks/sdk_worker_observer_extension_2026-11-24.sdn`.
