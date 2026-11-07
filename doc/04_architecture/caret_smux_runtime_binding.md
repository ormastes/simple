# Caret runtime binding through the existing smux owner

Status: implementation resumed; authored adapter/reference changes remain
unverified. Positive runtime binding source composition remains incomplete.

## Continued implementation on release 862d9e361534

The user resumed full implementation after the bounded source landed. The
current integration branch is `work/caret-orchestrated-session-binding-20261107`.
It now includes the merged group-stream source dependency at release
`8028e75917289a50b31bb695cbb5fe6f8c528667`; broker/stream consumer execution
qualification remains pending.
The first consumed repair makes the hosted `--request` client recognize the
exact authenticated capability SDN response. Its legacy text predicate stays
unchanged; discovery does not certify an executable binding.

Controller `dispatch` and `inspect-execution` are separate from the existing
V1 metadata commands. Generic resolved dispatch is not AgentSession execution:
the retained AgentSession must bind authorized task content, repository
revision, immutable image, installed CLI evidence and workspace ownership
before a runtime result can be projected into a Caret session.

The actual Caret entrypoint now routes `dispatch`, `resume-execution` and
`inspect-execution` through `orchestrator_execution_client_v2`. It invokes the
configured absolute compiled controller once, with protocol transport bounds
of 120000 ms for dispatch/resume and 30000 ms for inspection. The shared V2
reply codec validates canonical outer fields and the nested-response digest;
the client additionally validates the host V2 observation and correlates host
operation, plan and semantic request. Prepared state uses its exact five-field
schema. Nonzero exits, timeout, stderr, malformed data and saturated capture
retain the original UID as unconfirmed; none triggers an automatic retry.
The outer Caret result always keeps completion unobserved. Native boot facts
remain in the host scope; an internal runtime fence hash is not boot evidence.

The provider attachment opener must run in the persistent smux process. Host
resolution can reopen protected retained execution state there, but a native
pipe reference cannot arrive from a one-shot host subprocess or a wire reply.
Provider inspection/policy checks precede opening; canonical ownership transfers
to the existing pane exactly once. The provider never starts a second reader.
Host observation/load and provider session APIs are being finalized by their
owners; this branch must not substitute serialized observations or argv plans.

Windows Docker and Linux Podman are both selected through the common Simple
Container API. Caret/smux consume its typed execution and stream adapter; engine
CLI construction stays inside provider implementations. Agent CLI invocation
adapters are separate: their exact argv becomes immutable container workload
input after trusted image/CLI evidence is resolved.

The daemon's new owned transport transfers `PipedProcessOwnedTransferV2`, which
retains both `GroupProcessStreamOwnerV2` and the canonical pipe reference. A bare
reference would lose helper-budget/request provenance. `group_root` and
`group_identity` are additional process-local reference authority fields; pane
comparisons use the shared canonical equality helper instead of comparing PID
and generation locally.

For the group-owned profile, the reference's diagnostic PID identifies the
broker, not the engine helper child or container. The adoption API's legacy
integer return cannot prove attach success or correlate a child-written owner
file by PID equality. Binding receipts use exact runtime identity and retained
request/owner identities; actual stream bytes supply separate observation.

| Boundary | Ownership classification |
|---|---|
| Controller/host observation to Caret | Encoded fact copy; never native stream authority |
| Provider attachment result before adoption | Provider-owned bundle, including cleanup-bearing failure without a reference |
| Bundle validation and adoption preflight | Scoped loan; caller retains ownership on refusal |
| Successful adoption | Owned transfer to the canonical smux pane; provider relinquishes after acceptance |
| Pane/revision/checkpoint snapshots | Process-local copies of identity; no new reader or independent cleanup authority |
| Host resource release | Retained grouped reap receipt acknowledged by the host ledger, never inferred from close or EOF |

The host action-lease/reap acknowledgement interface is being finalized before
production attachment admission and resource release are enabled. The pane
can invoke exact helper cleanup, but retains the cleaned owner until a verified
acknowledgement exists. Source snapshots cannot substitute for that authority.
A new configured service mode must fail closed when required owners are
unavailable; it cannot silently downgrade to the legacy server.

The current canonical lifecycle limitations below remain until the daemon's
exact POSIX process/group-owner integration is admitted. Client decoding and
immutable intent validation can proceed independently; successful attachment
rollback and complete lifecycle qualification require that owner integration.

The existing server authenticates a local owner token and dispatches textual
commands. It does not install the complete CoreMux framed server, despite
having reusable CoreMux contracts, target validators, and request-ledger code.
The new boundary is a negotiated versioned textual compatibility adapter.
It must not claim a complete framed CoreMux provider.

## Authority and ownership

| Concern | Authoritative owner |
|---|---|
| Desired workload, assignment and immutable request | Controller |
| Grant verification, protected retained execution and fresh runtime facts | Host |
| Explicit trusted runtime policy and exact-ID attach authorization | Container provider |
| Output helper reference, rendering and lifetime | Existing smux pane owner |
| User selection and presentation | Caret client |

The local server token is local owner authentication. It is not a remote host
grant or proof that an execution is running. A serialized runtime binding is
expected identity, not observation or permission. The server composition
supplies protected state roots and provider policy; bind requests cannot
choose a journal root, executable, argv, observation or stream capability.

The approved trusted-local-administrator mode selects an explicit absolute
provider executable/store and verifies observed runtime identity. It is
honestly unsealed. Sealed static-ELF admission is a separate mode and is not
silently required of dynamic Podman or silently downgraded when unavailable.

## Process and stream boundary

The current piped process registry is reused through the daemon lane's agreed
generation-bearing reference API. A copied raw PID is insufficient: it can
alias a reused registry entry. The shared process owner must check generation
on spawn/read/write/liveness/close and make duplicate close safe. No provider
private process table or second supervisor is added.

`PipedProcessRefV1` is process-local authority for one registry lifetime. It is
never a persisted or remote receipt, and cannot be reconstructed from serialized
PID/generation values after a process restart. In-memory pane/checkpoint copies
retain its generation; future request composition must also reject stale service
and child incarnations.

The provider's proposed terminal session carries that canonical reference,
exact RuntimeIdentityV1 and policy/observation correlation. The final public
provider method names remain owned by the provider lead until reviewed. The
shared `sosix_process_*_ref_v1` process API names are agreed with the daemon lead.
Smux adopts the reference into its authoritative pane state; its existing
pane_poll_state remains the only reader. Every clone/rebuild and cleanup path
must preserve reference authority and pane child incarnation.

The first provider capability is output-only: Podman attach fixes `--no-stdin`
and `--sig-proxy=false`. Input and geometry are refused. Closing the helper must not request
container stop/remove. A relay identity is never the container agent identity.
The existing stream is UTF-8/text: this change must not claim arbitrary binary
byte preservation or container geometry control without separate evidence.

The baseline unowned POSIX canonical close returns `process_close_unsupported` and
retains the exact registry slot without signalling or closing/freeing it.
Other raw reapers prevent a generation alone from proving kernel PID/group
ownership after reap. Smux preserves the pane and cleanup authority on this
refusal. The registry has 16 slots; retained owners consume capacity. Successful
POSIX teardown requires further exact group ownership work and remains blocked.
Windows HANDLE/job cleanup is a separate mechanism and is not qualified here.
This limitation blocks a provider-attach lifecycle built from unowned refs.
The continued implementation uses the separate group-owned stream profile;
it does not weaken or reinterpret the baseline refusal.

Baseline unowned POSIX canonical liveness similarly returns `process_liveness_unsupported`
without waiting, reaping or signalling. Adoption uses the separate
`sosix_process_validate_piped_ref_v1` exact registry lookup, which proves only
that the process-local owner reference is present. It does not establish a
live helper or completed attachment. Stream EOF proves drained output, not
process exit. Both exit and teardown qualification remain blocked.

The owned profile transfers `PipedProcessOwnedTransferV2`, retaining both the
canonical byte reference and `GroupProcessStreamOwnerV2`. The pane validates
the bundle before publication. The provider keeps authority if adoption is
refused. Successful helper cleanup retires the native reference exactly once;
the pane then retains owner provenance in `helper_cleaned_awaiting_release`
until the host acknowledges the exact reap receipt. This state rejects input,
replacement, removal, reset and server shutdown. It performs no subsequent
byte read, liveness or close operation on the retired reference.

Authenticated `stop-server` now checks retained canonical references and owned
bundles before accepting shutdown. The future configured binding context must
also account for provider cleanup owners that never acquired a pane or byte
reference. A pane-only guard is insufficient once that context is installed.
Neither cleanup success nor EOF authorizes releasing host capacity.

## Binding transaction

Authenticate before decoding or effects. Validate the bounded versioned
request and exact target ownership/incarnation. Resolve the retained immutable
request from the configured owner, obtain fresh host/provider evidence, and
reject unsupported capability before journal begin or pane mutation.

The immutable replay payload must cover both runtime binding and concrete
smux target. Existing SessionRuntimeBindingV3 lacks concrete session/window/
pane incarnation, so its digest alone cannot authorize redirectable target
arguments. Canonical full-request reservation must reject changed target or
payload under the same operation ID.

Retain payload and begin the existing V2 operation before opening/adopting the
helper. Commit success only after the pane owns its real reference. Preserve
unknown outcome for reconciliation; never retry a spawn simply because a
reply was lost. An identical replay returns the retained outcome without a
second attach. Runtime/provider/host boot changes invalidate stale bindings.

Detach releases a client view. Input, geometry, cancellation and termination
remain distinct authorities. Transport teardown closes only the owned helper;
it cannot substitute for a host cancel/terminate operation or claim exit.

## Current public boundary and acceptance

After existing token authentication, `runtime-binding-capabilities-v1`
truthfully advertises the unavailable runtime-binding owner. Known
`bind-existing-runtime-v3` requests return explicit unsupported receipts with
no committed operation or owned stream. The ordinary unauthenticated remote
dispatcher does not gain access to either route. Both remain within existing
request/reply limits and reuse the server's length-framed replies.

These are useful production-route refusal tests, not positive binding proof.
The same integration branch must compose the real owner before it is offered
as a completed feature. Positive acceptance needs a real provider-created
runtime, owner-resolved observation, exactly one adopted stream, fresh nonce
through the existing pane reader, independent provider inspection, stale
generation rejection, replay without respawn, and detach without termination.

No runtime builds or tests have run for this integration. Full host/provider
composition and an admitted product toolchain remain prerequisites.
