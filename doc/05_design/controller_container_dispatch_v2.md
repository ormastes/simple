# Signed controller dispatch through the Simple Container API

The public controller execution route consumes `ControllerDispatchRequestV2`.
The packet retains the existing assignment, original controller and host
operations, four independent signed grant/approval pairs, and one explicit
`ContainerExecutionRequestV2`. Linux uses `linux-podman`; Windows uses
`windows-docker-process`. No engine fallback or direct application engine call
is permitted. Platform leaves alone decode opaque request bytes and construct
engine commands.

The codec checks canonical shape and transitive operation/plan/scope bindings.
It does not authenticate signatures or assert that opaque request bytes describe
a valid platform request. The controller owner verifies all four pairs against
its installed authority snapshot and actual Unix-millisecond clock. It invokes
the configured host command core's `host-validate` and matches the actual
Container API projection to request digest, UID, attempt, operation, resources
and signed duration before admission. The host independently repeats authority,
deadline, resource and provider checks before effects.

Authorized physical-host aliases and observed native machine identities remain
separate. Native boot and persistent service incarnation are explicit modes.
The all-field scope hash is an internal compatibility fence, not a boot proof.
New production dispatch uses V2; existing V1 payloads are not silently rehashed
or relabeled as V2. Generic resolved dispatch rejects a UID with a retained
AgentSession source until the actual immutable session resolution chain exists.

The controller uses its existing operation journal and immutable content
objects. The host uses its own existing journal and capacity ledger. Admission,
prepare, assignment commit and execution retain distinct authority domains even
in the local-inprocess route. Repeated dispatch inspects an already committed
assignment; explicit resume requires the host's exact still-admitted response
and fresh proofs. Unknown, missing or observed execution is never permission
to create a new attempt. Errors after possible effects retain identity and
request reconciliation, including stdout publication failures.

`HostHelperPlanV1` binds a separate helper operation to its exact parent
operation, assignment, scope, launch-template request and signed aggregate
budget digest. `ControllerParentBudgetV1` bounds workload plus every retained
helper in the same physical ledger. CPU overhead is nonzero accounting; the
current group process owner has memory enforcement but no kernel CPU quota.
That missing enforcement remains an explicit full-feature requirement.

`ControllerExecutionReplyV2` preserves the nested host response and its digest;
it always reports `completionObserved=false`. Caret validates the nested host
observation as well as outer identity. A start or inspection observation is not
completion. Qualified terminal wait evidence must be retained before cleanup,
and independent exact-object absence is distinct from a destroy return code.

Source checkpoints contain authored integrity/authorization scenarios, not
runtime qualification. Full public-process acceptance, actual platform engine
effects, persistent Windows quarantine/reconciliation, immutable AgentSession
resolution, interactive stream ownership and remote completion remain required
integration work. No compiler retry, native acceptance run, coverage claim or
production readiness PASS is implied by this design or a source commit.
