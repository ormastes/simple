# Caret local controller submission and inspection

Caret's existing `run_main_args` dispatcher now consumes the local controller
protocol through a real child-process boundary. It routes `orchestrator` to
`run_orchestrator_cli`, which validates the request, invokes the explicitly
selected compiled controller once, and validates the structured SDN reply.
This is a client for retained metadata. It does not start a runtime workload,
establish a remote authenticated channel, or attach a terminal.

REQ-CARET-CONTROLLER-001: accept only explicit absolute executable/state paths,
valid controller and request identities, and exact submit/inspect arguments.
Submission carries an absolute source path and namespace/name selectors.
Inspect carries no submission selectors. Invalid requests fail before process
execution. Argument values remain separate argv elements, including spaces.

REQ-CARET-CONTROLLER-002: accept only strict SDN with the exact local-controller
kind/version, matching controllerId/requestUid, a valid source digest, and the
selected operation's metadata status. Require executionAuthorized false.
Inspect must report runtimeState unobserved and terminationObserved false;
assignment and desired-state relationships must be internally consistent.
Do not reinterpret a retained binding or cancellation intent as execution,
readiness, termination, a provider handshake, or permission.

REQ-CARET-CONTROLLER-003: after invoking the child, timeout, nonzero exit,
capture saturation, stderr, malformed SDN, or invalid identity/schema makes
completion unconfirmed and reconciliation required. Preserve the caller's
original controllerId and requestUid even when the controller error lacks
identity. Never generate a replacement UID or automatically retry. The caller
may inspect that same UID through the explicit inspect command.

The controller protocol is owned by `app/orchestrator/local_controller.spl`
and `app/orchestrator/inspection.spl`. Their existing source was inspected
read-only and the orchestration lead agreed these command shapes. This patch
does not copy or independently reimplement the controller store or journal.
The controller owner is responsible for admitting and compiling that closure.

The process facade applies a 10-second child execution budget and 64-KiB
capture cap. This is not an end-to-end caller latency guarantee: the facade's
process-governor admission may wait before the child starts. Strict parsing
also limits depth and document complexity. CLI output is a canonical SDN
projection of the checked reply; arbitrary stderr and rejected reply bytes
are not echoed. The explicit executable pathname is configuration, not a
pinned executable identity or authenticated provider capability.

No new service loop, retry scheduler, PTY reader, grant, or runtime union is
introduced. Existing pane-team preflight, smux ownership, and distinct
detach/cancel/terminate/input/geometry authorities remain in their owners.
The new route does not eagerly probe a controller during ordinary chat startup;
its process call and parser execute only for an explicit controller command.

Validation uses production-import argv/decoder/refusal regressions in
`test/03_system/app/llm_caret/feature/orchestrator_client_spec.spl`. These tests
do not claim a compiled-controller or distributed-execution round trip. The
full system scenario requires the actual compiled Caret/controller/host
composition, durable owner evidence, real provider observation, and smux
output. Runtime tests and generated-manual tooling remain UNRUN until an
admitted product runtime and the controller binary are available.

The earlier checked provider adapter investigation remains deferred: V3 pinned
processes lose workspace/auth environment, V4 supports explicit cwd/env but
requires a consumed owner-bearing lifecycle, and Linux static-ELF admission
does not cover scripts or dynamic Claude/Kimi binaries. No orphan checked
launch helper or mux V3 contract-only breadth is admitted here.
