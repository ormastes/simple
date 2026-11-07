# Finite local host composition

Current integration status: work in progress, NOT_RUN. The user's subsequent
requirement is mandatory: Windows Docker and Linux Podman both run through the
shared Simple Container API V2. This host root and command core now use only the
shared observe/open/project/recover/read facade and the shared signed executor.
Backend policy and native commands remain in platform leaves. The provider
enforces a request/action-bound absolute admission deadline after identity observation.

`host_local_command_v1(args)` returns `HostLocalCommandReplyV1{exit_code,output}`.
The canonical orchestrator app and its configured same-process controller target
call this same library core. Controller and host retain independent journals.
There is no new scheduler, listener, global mutable owner or daemon-liveness claim.

Commands:

| Command | Arguments after command | Successful canonical SDN |
|---|---|---|
| `host-enrollment-observe` | installed machine parent, HostConfig file, engine policy file | unsigned enrollment binding for issuer approval |
| `host-local-init` | same three paths, signed enrollment credential file | claimed private root and binding/claim digests |
| `host-status` | protected enrolled root | version2 scope, ledger fence, capacity and enrollment/provider identity digests |
| `host-validate` | protected enrolled root, ContainerExecutionRequestV2 file | API-projected identity/resources, executionAuthorized:false; no capacity journal |
| `host-prepare` | protected enrolled root, immutable signed request file | existing HostPrepareResponseV1 |
| `host-execute` | protected enrolled root, immutable signed execute file | HostExecutionObservationV2 |
| `host-inspect` | protected enrolled root, operation ID | exact prepared state or freshly inspected retained execution observation |

Failure output is `host-local-error` version 1 with `action`, `operationId`,
`recoveryRequired`, and `error`. Exit 1 is rejection before any new workload
effect is known; exit 2 requires reconciliation and never grants a retry.
Initialization failures are conservatively exit 2 because a claim may remain.
Successful preparation/execution is returned only after closing the exact writer.
Closure never stops a native resource or frees capacity.

The local administrator installs the trusted machine parent and public authority
policy. The same trust prerequisite applies to the controller's fixed root route;
an arbitrary caller-owned directory is not an authenticated machine authority.
The code uses private nofollow roots and bounded reads, with the existing
path-based trusted-ancestor limitation. It makes no descriptor-relative race
guarantee. The provider's explicit mutable-path policy is not a sealed executable.

Enrollment preflight calls the shared platform observer for actual machine/boot
identity and the provider's actual executable/user/store identity. The finite
path requires native-boot-incarnation-v1 assurance; a Windows boot counter cannot
be substituted for a native boot incarnation. Initialization recomputes
that binding, verifies the existing dual-role signatures, claims the unique native
machine slot, and retains the canonical engine policy. A runtime-ready record is
published only after those objects are read back and synchronized. Initial epoch
is 1 for that unique enrolled root. Reboot/provider drift refuses opening; it does
not create a replacement authority or adopt old workloads.

Opening checks the retained claim, root, binding/configuration/policy digests,
historical credential correlation, actual native identity, provider identity and
rootless capability. Only then does it open the existing capacity journal with
continuity established by those checks. Executing rows reopen as uncertain and
remain charged. Policy changes require an explicit future reconciliation path;
the opener does not silently accept a new policy or epoch.

Execution uses separate signed `host_execute_v1` authorization over the original
immutable reservation envelope with that derived action. The provider request's
semantic digest is recomputed, and its operation ID is compared independently.
The request, plan and signed packet precede the journal execution intent; create
and start follow it. Observations contain provider facts and authority correlation,
not authorization. The provider is independently inspected before success and
the observation is synchronized before responding. Failed/unknown operations do
not release capacity or launch another attempt. Inspect has no create/start path.

Prepared inspect returns exactly `version`, `kind: host-local-operation-state`,
`operationId`, `state: admitted`, `executionObserved: false`. This is a retained
journal fact, not permission to execute. The controller must revalidate a fresh
explicit execution request. Unknown execution without a retained observation
currently returns recovery-required; automatic reconstruction and cleanup remain
separate work.

The current finite root is strong-native-continuity only. Linux Podman and Windows
Docker plans route through the common API; enabling Windows requires the separate
actual persistent service incarnation and startup inventory/quarantine path now
under implementation. Device/workspace claims remain refused until their approved
identity and resource-accounting adapters exist. Helper admission, terminal
ownership transfer, service broker overhead, drain, terminal wait retention and
absence-based capacity release remain separate active source work.

The selected journal profile is `process-crash-v1`; the WAL does not claim
power-loss durability. No fsync claim about archived objects upgrades journal
durability. A changed boot/provider identity refuses finite reopening. The
persistent service path refreshes actual complete managed-scope inventory while
holding the same journal writer, retains unknown charges and records reconciliation
before admission. No runtime conformance or full host completion is claimed.
