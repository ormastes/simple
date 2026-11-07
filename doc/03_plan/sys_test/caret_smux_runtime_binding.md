# Runtime binding verification handoff

## Current local composition checkpoint

The V3 exclusive in-process implementation and current limitations are in
`doc/05_design/smux_exclusive_runtime_binding_v3.md`. Added request, reply,
policy, immutable-store and authenticated adapter specs remain AUTHORED_UNRUN.
The configured socket system scenario exercises real process authentication,
vacant metadata target creation/retry and unplanned binding refusal. It is not
positive Container attachment evidence. The existing runtime reference spec
retains legacy V2 coverage and adds separate full-V3 settlement metadata
transitions; no typed ACK constructed in a pure test is native/ledger proof.

The historical dependency notes below describe earlier source checkpoints.
Current merged base is `47ffbb08154f40e166ffb385d99748c3463a9152`, including
the previous Caret checkpoint and all following shared dependencies.
Additional exact source dependencies: host resolver `a3826478ed7`, standalone
parent budget `3682a914381`, capability query
`8640674fdd8a1af65ae070f734c10ce0988e3db6` and its native preflight, helper
consumption/settlement `dd78e274ac5534ed4dd3e0241e513fd2e514c79c`, plus host
settlement hook `d6aedcb4471f2cae90718c6d76a82586a11348ed`. Root owns the
combined integration head (PR 7743) and final dependency closure. No source copy or
placeholder implementation replaces these owners. Runtime verification is
still NOT_RUN; the campaign-wide five-core/build allocation restriction remains.

## Historical checkpoint evidence

Status: implementation resumed from release commit
`862d9e361534c1a13f83a2f43da06e07847df5af`; executable verification remains
unrun. Positive runtime-binding source composition is incomplete. No
feature-complete or full-system PASS is asserted.

Canonical process API dependency: daemon source commit
`65b04829656503ad9715e6e0fb12474094585710` on
`work/piped-generation-owner-20261107`. This is an immutable source dependency,
not runtime admission. Integrate it before building the consumer; its exact
validator and POSIX unsupported lifecycle results define the retained unowned
reference test boundary. The new owned-transfer consumer now integrates
`GroupProcessStreamOwnerV2` and `PipedProcessOwnedTransferV2` from merged PR
7721, release commit `8028e75917289a50b31bb695cbb5fe6f8c528667` (reviewed
integration head `8c20e88267dc3b207fe81cf5ad3e33ed214d77da`). The native no-child
classification prevention check passed in that lane; full broker/stream and
Simple consumer qualification remain unrun. This is source admission, not
application exec or attachment readiness.

The execution client additionally requires the actual shared controller reply,
Container scope/API and host observation V2 modules integrated at
`39e6058bdbd4c0169ec600433e02e2fc5aadbcc8` on
`work/container-api-provider-integration-20261107`. That source integration is
not yet landed and is held for a Windows provider finding outside this lane.
This Caret commit must be combined with those reviewed dependencies before
compilation or landing. The modules were checked against that concrete tree;
no substitute owner or local copy of its contracts is included here.

Continued implementation adds
`test/03_system/app/llm_caret/feature/smux_capability_client_spec.spl`: six
authored production-dispatch/client-classifier cases for strict capability
decoding and operation-specific exit classification. They are source-import
integration checks, not socket or compiled CLI evidence. A separate real
compiled `--serve-owner-file` / `--request` scenario is authored with
mandatory private fixture and binary inputs; it must fail when those inputs or
the actual transport are absent. No runtime check is authorized by this plan.

That actual process/socket scenario is now authored as
`smux_capability_socket_spec.spl`, using shared test-only support in
`test/helpers/smux_owned_process_fixture.spl`. It runs separate compiled server
and request processes, validates protected nonce/token publication, discovery
and refusal exit codes, authenticated stop, genuine stdout EOF and durable
terminal cleanup proof. It remains AUTHORED_UNRUN and requires the manual's
explicit compiled binary identities, private root and delegated resources.

The current production-route suite is
`test/03_system/app/llm_caret/feature/smux_runtime_binding_capabilities_spec.spl`.
It exercises real server dispatch for authentication ordering, exact absence
capabilities, refusal with unchanged owner state, exclusion from unauthenticated
dispatch, and existing frame limits. It must not be presented as positive
runtime attachment coverage.

`orchestrator_execution_client_spec.spl` adds seven authored source-import
cases for the consumed Caret execution CLI path: exact arguments and protocol
timeouts, effect-free request refusal, nested prepared/observed correlation,
scope-preserving output and uncertainty without retry. These synthetic wire
checks are not a substitute for the actual compiled Caret/controller process
roundtrip or signed host execution. Keep metadata V1 scenarios unchanged.

Pure reference-state regressions cover canonical-reference preservation,
same-PID/different-generation incarnation changes, revision publication and
rollback identity. Fourteen authored cases additionally cover the complete
group-owner bundle, cleanup-pending retention, authenticated stop admission,
and malformed pending-release input refusal. They use synthetic values only
as pure state data, never as native process authority.

The owned-transfer system scenario must exercise a real bounded group helper,
the actual smux adopter and sole pane reader, nonce output and EOF, one-shot
cleanup, and retained `helper_cleaned_awaiting_release` state. Cleanup success
retires the byte reference; further native operations on that reference must
be rejected. Host budget release remains a separate receipt-acknowledgement
gate. The absence of that owner must not be replaced with a test-created grant
or a fabricated release receipt. Failed startup must retain cleanup-bearing
outcomes even when no byte reference was created.

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

Source checkpoint checks: the direct environment/runtime guard passed for
working and staged changes, and the document-layout scan found zero executable
`*_spec.spl` files under `doc/06_spec`. These checks do not constitute an
executable test or production-readiness PASS.
