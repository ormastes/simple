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

The separate provisional Hello-qualified route also needs explicit propagation.
Its public launcher now accepts `--lifetime-ms=0 --memory-policy=monitor` for
post-readiness work, preserving the prior six-hour/enforce defaults. Binary and
index manifests receive both options; native-group preparation publishes the
same fields into its typed config. Monitor RUN-5 and legacy enforce RUN-4 are
accepted. Product compilation requests dynload, without claiming a provider was
actually loaded. Binary/index manifest replay re-emits a deterministic candidate
and compares it with retained bytes, refusing a changed requested policy before
dispatch rather than silently running the previous manifest. Reservations, poll intervals, attempt limits, source/runtime
bindings and the existing native cleanup budgets are unchanged.

Two focused shell regressions execute the production routing functions, config
publication, and final public-launch command with owner/emitter spies. They
observe zero/monitor at the binary, index and group dispatch boundaries, positive
memory reservations, forty requested threads and finite polling. Negative work
durations, unknown policies and obsolete manifest wires remain rejected. This is
argument-routing evidence, not native lifecycle or compiler qualification.

Pre-readiness Hello and manager-image contracts remain separate: their existing
runtime-root/profile authority and the image builder's 21600-second watchdog are
not made unlimited by these post-readiness options. A profile extension or formal
admission is still needed before claiming an entirely unlimited end-to-end run.
