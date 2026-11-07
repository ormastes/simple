# Charged AgentSession preflight

The controller retains an immutable association from an existing desired
AgentSession and pinned catalog to one distinct, ordinarily charged probe
workload. The probe is not a helper of the unresolved final session: that would
make its authorization depend on the image/CLI evidence it must produce.

## Implemented source path

`AgentPreflightBindingV1` binds controller/session UID, exact desired/catalog/task
digests, image and probe-producer digests, nonce, expected executable/provider,
OS/architecture/user, and the full scoped Container execution plan. All these
are expectations. None is installed capability evidence.

`AgentPreflightDispatchV1` contains that binding, the existing V2 dispatch packet,
and a separate signed grant/approval pair for `agent_preflight_authorize_v1`.
Its authorization operation preserves the original controller operation's
principal, project, host, environment, policy, revocation, session and resource
fields while binding the exact association digest. The existing four execution
proof pairs remain unchanged. Protected local policy and actual Unix milliseconds
are used at entry and again before host execution.

The public controller routes are:

- `preflight-dispatch <root> <controller> <session-uid> <packet-file>`
- `preflight-resume <root> <controller> <session-uid> <packet-file>`
- `inspect-preflight <root> <controller> <session-uid>`

The ordinary controller journal writer archives exact proof bytes, retains the
association object, and commits `controller_agent_preflight_v1` before calling
the existing controller-to-host dispatch core for the distinct child UID. No
new scheduler, resource ledger, provider command path or journal is introduced.
The association operation ID is stable per controller/session; changed payloads
cannot silently replace it. Generic dispatch refuses an associated child unless
the separate preflight authorization is supplied through the preflight route.

Replay explicitly recognizes the new metadata action, verifies its immutable
object and committed desired/catalog ancestors, and retains rejection of foreign
operation domains. Association recovery completes metadata only. It never
replays an unknown host launch.

Cancellation first publishes the child's sticky cancellation, when a child row
exists, then the desired-session cancellation marker. A crash between these
commits cannot revive the child. Before a child row exists, the parent marker
blocks later preparation and execution. This is cancellation intent and exact
reconciliation linkage, not termination evidence or permission to release
charged resources. Inspection preserves historical association after cancellation.

Reply kind `agent-preflight-execution` version 1 includes controllerId,
sessionUid, preflightUid, bindingDigest, status, executionReply and
agentSessionExecutionAuthorized=false. Status is association-retained or
probe-status-observed. The nested reply is the existing V2 execution observation;
neither outer status asserts probe completion or final AgentSession admission.

RuntimeClass policy explicitly admits Linux/Podman/rootless and
Windows/Docker/process pairs, refusing crossed engines and fallback. Policy
decoding alone does not establish platform capability or Windows continuity.

## Required subsequent consumed stages

The actual image probe producer, protected execution-host result signer, signed
probe-result acceptance, task-content authorization resolution and final
AgentSession request construction remain required. The result must correlate
the nonce and probe producer with actual CLI bytes/version, exact image,
configured-user observation, runtime identity and retained wait evidence.
Only then may the resolver call the admitted agent CLI/invocation contracts.
Expected association fields must never be promoted into an observed capability.
The current admitted CLI adapter accepts Codex, Claude and Kimi profiles only.
Gemini remains a required pending provider from the original scope; it is
explicitly refused until its actual observed CLI adapter and probe-result
validation exist. The expected-provider allowlist does not remove that work.

Executable workspace preparation additionally requires an actual protected
workspace/storage lease, exact file manifest, native identity/hash checks and
qualified user mapping/access. Linux rootless mode alone proves no UID mapping.
Windows uses its own ACL/access and persistent service continuity owner. These
conditions remain enforced by the common Container API and platform leaves.

## Verification

The binding, packet, authorization and journal SSpecs exercise real imported
code; journal cases create actual private roots and replay the same journal,
and authorization cases use actual SDK Ed25519 signing/verification. Runtime
policy and placement cases enforce the two explicit backends. All are authored
and NOT_RUN under the current compiler-attempt prohibition. No public-process,
Podman, Windows, complete probe or end-to-end AgentSession PASS is claimed.
Root owns integrated review/landing and later allocated verification.
