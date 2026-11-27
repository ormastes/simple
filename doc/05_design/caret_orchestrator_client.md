# Caret local controller submission and inspection

Caret's existing `run_main_args` dispatcher now consumes the local controller
protocol through a real child-process boundary. Metadata actions route to
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

## Separate V2 execution observation client

Continued implementation adds `orchestrator_execution_client_v2.spl` and
consumes it directly from `run_main_args`. Public arguments are:

```
orchestrator <absolute-controller> dispatch <state-root> <controller-id> <uid> <packet-file>
orchestrator <absolute-controller> resume-execution <state-root> <controller-id> <uid> <packet-file>
orchestrator <absolute-controller> inspect-execution <state-root> <controller-id> <uid>
```

REQ-CARET-EXECUTION-001: keep metadata V1 separate; validate exact V2 action,
absolute paths and identities before invoking the controller. Dispatch/resume
use its agreed 120000 ms transport budget; inspection uses 30000 ms. Both use
262144-byte capture with saturation treated as uncertainty. These budgets are
not signed effect deadlines, workload lifetime limits or governor admission
latency guarantees. Explicit resume is a caller request, never an automatic
timeout retry.

REQ-CARET-EXECUTION-002: consume the shared
`controller_execution_reply_decode_v2`, then the host-owned observation V2
decoder for `runtime-observed`. Correlate controller/UID and nested host
operation, plan and semantic request digests. A prepared report requires the
exact five-field host operation-state schema. Preserve canonical nested scope
and runtime facts; internal fence hashes remain distinct from native boot
identities. The configured controller and host owners verify signed packet and
grant authority; this client does not independently reverify those grants.

REQ-CARET-EXECUTION-003: every post-invocation error retains the original UID as
unconfirmed with reconciliation required. Output is the separate version-2
`caret-orchestrator-execution-result`; `completionObserved` is always false,
including an observed `exited` runtime phase. CLI exit 0 confirms correlated
facts, exit 1 requests reconciliation and exit 2 reports preflight/usage error.
Generic resolved dispatch cannot stand in for retained AgentSession image,
task, workspace and installed CLI resolution or terminal binding.

Seven focused scenarios and their manual are authored at the matching
`orchestrator_execution_client_spec` system-spec paths. They exercise production
client/codec source with synthetic observations and remain AUTHORED_UNRUN.
Actual compiled Caret/controller invocation, signed host execution and full
terminal acceptance remain separate required verification.
