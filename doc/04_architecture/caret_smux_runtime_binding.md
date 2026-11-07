# Caret runtime binding through the existing smux owner

Status: AWAITING_VERIFICATION for the authored adapter/reference changes.
Positive runtime binding source composition remains incomplete.

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

The current POSIX canonical close returns `process_close_unsupported` and
retains the exact registry slot without signalling or closing/freeing it.
Other raw reapers prevent a generation alone from proving kernel PID/group
ownership after reap. Smux preserves the pane and cleanup authority on this
refusal. The registry has 16 slots; retained owners consume capacity. Successful
POSIX teardown requires further exact group ownership work and remains blocked.
Windows HANDLE/job cleanup is a separate mechanism and is not qualified here.
This limitation also blocks a complete provider-attach lifecycle.

POSIX canonical liveness similarly returns `process_liveness_unsupported`
without waiting, reaping or signalling. Adoption uses the separate
`sosix_process_validate_piped_ref_v1` exact registry lookup, which proves only
that the process-local owner reference is present. It does not establish a
live helper or completed attachment. Stream EOF proves drained output, not
process exit. Both exit and teardown qualification remain blocked.

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
