# Runtime binding verification handoff

Status: awaiting verification, with positive runtime-binding source composition
still incomplete. No feature-complete or full-system PASS is asserted.

Canonical process API dependency: daemon source commit
`65b04829656503ad9715e6e0fb12474094585710` on
`work/piped-generation-owner-20261107`. This is an immutable source dependency,
not runtime admission. Integrate it before building the consumer; its exact
validator and POSIX unsupported lifecycle results define this test boundary.

The current production-route suite is
`test/03_system/app/llm_caret/feature/smux_runtime_binding_capabilities_spec.spl`.
It exercises real server dispatch for authentication ordering, exact absence
capabilities, refusal with unchanged owner state, exclusion from unauthenticated
dispatch, and existing frame limits. It must not be presented as positive
runtime attachment coverage.

Pure reference-state regressions cover canonical-reference preservation,
same-PID/different-generation incarnation changes, revision publication and
rollback identity. They use synthetic values only as pure state data, never
as native process authority.

The authored native-consumer scenario is
`test/03_system/app/llm_caret/feature/smux_runtime_terminal_transport_spec.spl`,
with its manual in the corresponding `doc/06_spec/03_system` path. It uses a
real bounded helper for exact owner validation/adoption, fresh output,
tail draining, explicit EOF, stale-generation refusal, retained POSIX close
refusal, and output-only input/geometry refusal. Run it only after the canonical process
owner is admitted. It is AUTHORED_UNRUN, not Podman conformance evidence.
POSIX liveness/exit, successful teardown and duplicate close after release are BLOCKED_CAPABILITY:
the current canonical owner returns `process_close_unsupported` with no signals
or slot release. Run the scenario in an isolated test process; its two retained
slots are intentional uncertainty evidence, not completed cleanup.
Liveness returns `process_liveness_unsupported` without waiting or reaping;
the exact-reference validator checks only registry existence/generation.
Fresh delivered bytes and drained EOF do not prove a helper has exited.
Restart recovery and the full legacy smux regression
suite remain additional required verification; they are not covered by this
one positive helper scenario.

Full positive binding remains the system acceptance lead's gate. It requires
the actual protected host resolver, provider-owned exact-ID terminal session,
configured authenticated smux composition, immutable target-bound journal
payload, one actual reader, a fresh output marker, independent runtime inspect,
replay without another helper, stale host/provider/target rejection, and
helper detach without workload termination. Missing owners fail the gate;
they are not replaced with locally constructed success receipts.

Interactive input and resize are unsupported in the first output-only scope.
They require separately admitted create/tty/stdin capabilities and distinct
input/geometry authority, followed by real interactive regression tests.

Root must supply an admitted producer and allocate within the five-core total
CPU limit before any build or executable verification. Record exact source
and dependency SHAs, binary identities, commands and outcomes. Run each
accepted check once; repeat only after a relevant source change or new failure
evidence. Generated-manual tools and full-suite execution remain NOT_RUN.
