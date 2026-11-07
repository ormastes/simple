# Caret public controller metadata acceptance

Status: AUTHORED_UNRUN. This is the first public CLI slice of the accepted
distributed-execution system plan. Full execution acceptance remains incomplete.

## Scope and entrypoints

Run actual compiled `src/app/llm_caret/main.spl` and
`src/app/orchestrator/main.spl` products. The former must enter the landed public
`orchestrator` route, which launches the configured controller exactly once per
request. The test never calls the Caret decoder, controller command dispatcher
or controller store owner to perform an action.

The controller interface is `local-init <trusted-parent> <controller-id>`,
`submit <state-root> <controller-id> <uid> <source-file> <namespace> <name>` and
`inspect <state-root> <controller-id> <uid>`. Public Caret prepends
`orchestrator <absolute-controller-binary>` to submit/inspect. The selected
AgentSession fixture is `caret/review-simple`; source and state paths deliberately
contain spaces. Local metadata is not remote authentication or launch authority.

The real controller closure and existing
`test/fixtures/orchestration/caret_agent_session.sdn` landed in PR #7578 at
`a6dca22ee32da27ff9e45a67ba86ae3ef587074e`; this acceptance change is based on
that revision. Source dependencies are present, but product binaries and admitted
execution remain unqualified. Do not copy unmerged main-workspace production files
or fabricate a controller to make tests pass.

## Requirement traceability

| Requirement subset | Scenarios and independent evidence | Remaining gap |
| --- | --- | --- |
| CARET-01 public metadata client | Fresh-process submit/inspect; exact controller/UID/digest; relative executable and usage refusals | IaC execution, signed host dispatch, provider launch and terminal binding |
| DAE-03 reused durable operation journal | One completed committed desired-input operation; raw retained source; identical replay; changed-input refusal; unchanged WAL CURRENT | Whole-service crash recovery, bounded dispatch and provider-effect deduplication |
| OPS-01 metadata inspect/correlation | Explicit unbound/unobserved state; wrong-controller refusal; original UID preserved on unconfirmed responses | Live runtime state, cross-host logs and full audit correlation |

Every row maps to
`test/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.spl`
and its mirrored authored manual
`doc/06_spec/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.md`.
Six authored scenarios are not six executed or passing cases.

## Independent oracles

Parse outer and nested SDN with the generic strict parser, independently of the
product's receipt decoder. Require matching identities and `executionAuthorized:
false`. Positive inspection remains `unbound`, `intent-retained`, `unobserved`,
`terminationObserved: false`, and `desiredState: active`.

After child processes exit, separately replay the existing generic V2 operation
journal and release its exact temporary observation lease before assertions.
Require exactly one completed desired-input operation, decode its V2 envelope,
verify its retained payload digest, and independently parse the retained metadata
object's controller ID, workload UID and source digest. Compare the raw retained
source with the original input. This does not invoke the controller store owner.
An orphan source object alone cannot satisfy the oracle.

Read the raw bounded `journal/database-wal/CURRENT` before and after replay or
refusal. Identical replay and invalid requests must not publish a new revision.
The oracle's temporary lease does not change CURRENT. This proves the scoped
metadata mutation behavior, not power-loss durability or absence of native jobs.

## Preconditions, artifacts and execution

Require absolute Linux paths in `SIMPLE_CARET_ACCEPTANCE_BINARY`,
`SIMPLE_ORCHESTRATOR_ACCEPTANCE_BINARY` and
`SIMPLE_ORCHESTRATOR_ACCEPTANCE_ARTIFACT_ROOT`. Require the exact binary pins in
`SIMPLE_CARET_ACCEPTANCE_SHA256` and `SIMPLE_ORCHESTRATOR_ACCEPTANCE_SHA256`.
Both binary hashes are checked around public subprocess actions. This detects
observed file replacement; it is not atomic executable pinning or admission.

Fixture setup proves the controller's local-init route and Caret's canonical
usage-refusal route. Missing binary/input/hash, malformed output, timeout, empty
or saturated capture, and unsupported commands fail/block; none becomes a skip.
No shell wrapper, source interpreter fallback or test-only controller is used.

Each scenario gets a private evidence directory. Retain the fixture manifest,
argv, raw stdout/stderr, exits, binary hashes, submitted source, journal and
retained objects there. Failed subprocess output is written before parse/status
assertions. Processes are bounded and reaped by the standard process owner;
retained directories are intentional evidence, not a running daemon. No shared
directory or unrelated process is cleaned up.

Root must supply source/producer/runtime provenance and grant a build slot.
Use the current native-test guide's `--native-backend=llvm` or Cranelift route,
actual-execution assertions, no cached/session-shared success, retained artifacts
and `SIMPLE_NO_STUB_FALLBACK=1`. Do not use the old unadmitted producer or interpret
source discovery/loading as execution. Record actual binary case results.

After executable availability, run existing `spipe-docgen` for the affected spec,
require zero stubs and review the generated visible steps/folded executable.
Until then the manual is authored, not generated evidence. Metadata success cannot
close the separately blocked Podman, smux, host execution or RUN acceptance gate.

Owner: Astra system acceptance. Sol authored the visible scenarios/manual from
the frozen metadata-helper interface; Astra reviews helpers, assertions and manual.
Root performs independent exact-head review and coordinates dependency landing.
