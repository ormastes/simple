# Manager work duration must be independent of control leases

The managed Phase3/Phase4 route previously rejected lifetime zero, and its
inventory-backed manifest emitter silently assigned every task a 24-hour work
timeout. Passing a zero outer watchdog timeout therefore did not make the
compiled manager's work duration unlimited.

The shared work-deadline contract uses zero as an explicit unlimited sentinel.
Phase ownership and native group polling preserve that sentinel. Validators
accept zero only for useful-work duration; finite control, liveness, startup,
observation and cleanup budgets retain their existing validation and behavior.
In particular native group cleanup remains 30 seconds after cancellation.

Inventory manifest emission accepts optional `--work-timeout-ms N`, followed
by optional `--memory-policy enforce|monitor`, before `--manifest`/`--`.
Omitted options retain the prior 24-hour/enforce defaults and cache identity.
Changing either policy participates in the task identity. Managed phase,
binary, acceptance-suite and index manifests carry the selected work duration.
Native groups carry it through their separate request codec.

This scope is post-Phase2 managed work. The separate Stage2 manifest emitter
retains its existing seven-day task timeout; this change does not claim every
bootstrap route is unlimited. Positive memory and reserve fields describe
capacity admission and concurrent reservations, not an RSS kill threshold or
an arbitrary host-headroom stop.

Phase3/Phase4 product compilation explicitly uses dynload for LLVM then
Cranelift. Bootstrap manager support executables retain their existing
self-contained one-binary packaging; this is not a fallback for product work.

This checkpoint depends on the separately owned generic/grouped memory-policy
field and codec changes, Linux native owner zero-timeout change, and generic
ProcessObservationV4 zero-work-deadline change. Those must be integrated into
one reviewed candidate before compilation or deployment. No frozen producer
source or old cache is patched in place.

Validation completed: shell syntax and the actual managed-phase launch script
under emitter/owner spies. The regression observes two zero-timeout/monitor
manifest invocations, rejects a negative timeout before dispatch, and retains
the existing stale-pin/changed-manifest refusal cases. This is argument-routing
evidence only; native capacity, image and worker lifecycle qualification is
UNRUN. SSpec tests cover exact deadline boundaries, unlimited work beyond the
former caps, finite cleanup independence and real manifest encode/decode with
policy-sensitive identity; their execution awaits an admitted runtime.
