# Standalone Caret container sessions through the common owner

Status: implementation in progress; SOURCE_ONLY, NOT_RUN. No build, native,
bootstrap, test or docgen campaign is authorized in this lane. This is separate
from the orchestrated Windows V5 admission and geometry work.

## Accepted scope and actual seam

The standalone `cs --container` command must work without an orchestrator or
fabricated distributed grant. Linux selects Podman and Windows selects Docker
process containers in the library. Caret supplies typed image/guest argv and
mount intent. It must stop constructing engine argv, spawning that engine in a
pane and maintaining its own container-cleanup registry.

The current production chain is `cs_dashboard::_cs_launch_in_container` to
`cs_container_argv` to `pane_spawn_at`. The replacement is an authenticated
existing-smux local request, a retained common Container owner, then adoption
into the existing sole pane reader. Provider native handles are never returned
over a wire or reconstructed from IDs. A failed adoption returns the actual
cleanup-bearing owner.

## Frozen names

* `LocalContainerMountV1`: host_path, guest_path, read_only.
* `LocalContainerRequestV1`: image, executable, argv, working_directory, mounts,
  environment, network, cpu_millis, memory_bytes, terminal_mode, cols, rows.
* `local_container_request_validate_v1`, `local_container_request_bytes_v1`,
  `local_container_request_digest_v1`, `local_container_request_decode_v1`.
* `LocalContainerOwnerV1` is an opaque retained capability; no request decoder
  creates one. Start/bind/cleanup turns retain every post-effect obligation.
* `ContainerLocalExecutionBindingV1` is a distinct versioned local domain;
  it is not a renamed `ContainerExecutionBindingV3` or a managed Host receipt.

Requests are canonical SDN. An executable and argument boundaries are exact,
including empty arguments. Guest executable mapping is provider/installation
policy: a host Linux executable path cannot be blindly reused in a Windows
image. Mount lexical validation does not establish symlink or handle authority.
Actual source admission and guest destination construction belong to provider
owners before launch.

## Authority, accounting and lifecycle

An actual protected local policy owner plus the existing authenticated smux
principal admits local execution. It observes the exact provider/store identity
and grants only configured workspace, network and resource limits. It is not
`LocalAuthorityPolicyV1`, which only supplies distributed public verification
material, and it is not `WindowsPrimaryConnectionVerifiedV2`.

The installed provider scope determines whether capacity is standalone or a
managed pool. A caller flag, alternate directory or request-supplied budget may
not change that domain. Managed scope uses the existing authoritative pool
reservation or refuses before effects. Standalone workload and transport
reservations require one retained writer and real accounting. Reuse existing
WAL/retained storage and reservation machinery; no parallel journal framework,
daemon or process table. Resource charges survive uncertain publication/open
and release only after the appropriate actual transport/workload cleanup.

The common terminal V2 operations remain the read/cleanup seam. Smux owns the
sole reader after successful adoption. Local input/geometry authority must be
separate from managed Host grants and retain the same native generation,
revision and before-effect checks. Closing a transport never proves the
container workload absent; exact native identity and provider absence are
separate gates. Copied values cannot acquire another reader or release twice.

## Ownership and integration order

The Caret lead owns new local-session contracts/owner/provider modules and
`cs_container.spl`, `cs_dashboard.spl`, and the narrow `pane_backend.spl` hook.
Windows V5/no-connection files and Windows geometry are owned by their existing
leads. Shared terminal, exchange, adapter and smux registry edits require their
interface agreement before mutation. Frozen foundation INDEX is untouched.

1. Canonical request contract and real pure specifications.
2. Protected standalone policy and authoritative capacity-domain admission.
3. Actual provider create/start/terminal/stop/absence with retained failures.
4. Existing-smux local binding/input/geometry/settlement integration.
5. Replace the production Caret caller and remove app-owned engine/registry.
6. Independent source review of the complete consumed path and authored manuals.

No individual contract or refusal-only stage is feature completion.

## Evidence and remaining gaps

Author executable specifications for exact argv/mounts, pool-bypass refusal,
resource exhaustion, stale aliases, failed adoption, one reader, interruption,
transport cleanup, workload absence and release. Native Linux and Windows cases
require actual fixtures and must not pass through unsupported-host skips.
Manuals remain AUTHORED_NOT_RUN until an authorized admitted-runtime campaign.

At design freeze no standalone protected Windows policy factory or established
managed-pool discovery seam has been found. Existing enrolled Host factories
cannot substitute for these. Native runtime export approval remains external
to this source-only lane; no new exports or policy edits are authorized.

## Provider-scope admission prerequisite

The shared selector must live at a machine-authoritative installation location,
not beneath a caller-selected local or enrollment root. Its retained writer
serializes mode admission for the physical capacity scope. The selector binds
the actual observed provider identity to either one standalone budget authority
or an enrolled Host authority. Multiple providers on the same machine require
one physical budget or explicit disjoint delegated budgets; separate engine IDs
are not independent capacity. Both local open and Host enrollment must consume
this selector before reserving capacity or creating a workload. Missing,
unreadable, stale or ambiguous selector evidence means unknown, not standalone.

Neither current Host enrollment nor WindowsPrivateRootV1 establishes this
machine-global location: the latter proves a retained chosen root's ownership
and DACL. An independently chosen protected directory cannot establish that no
other enrollment controls the engine. The local implementation must not install
a private selector and treat its absence elsewhere as unmanaged discovery.
The Host lead owns the eventual narrow enrollment consumer, after the actual
machine-root or delegated-budget authority factory is agreed and implemented.

## Windows local terminal boundary

The agreed new lower module is
`std.nogc_sync_mut.io.windows_local_connection_admission_v1`, containing private
constructor `WindowsLocalConnectionVerifiedV1`. The local owner must bind its
actual protected policy, exact reservation, observed runtime/TTY, and native
one-use consumption receipt. The exchange hook is `begin_local_v1(admission)`;
no remote `WindowsPrimaryConnectionVerifiedV2` or synthetic remote connection
plan is accepted as local authority. Shared exchange edits remain reserved to
the Windows lead until this capability's fields and claim contract are frozen.

The existing native journal consumption primitive restricts names to
`primary-connection-consumed/<id>` but does not interpret payload authority.
A separate local journal may use that primitive with a distinct canonical
`local-container-attach-consumption-v1` payload after genuine reservation.
Publishing arbitrary bytes alone still confers no launch authority. Actual
claim success is one-use; claim failure retains uncertainty. Terminal transfer
needs a versioned local provenance arm and actual owner, not remote metadata
with renamed fields. Transport closure and workload absence remain distinct.

The Windows lead reserved a new lower `container/service_domain_v1` module for
`ContainerServiceDomainV1.Managed(HostServiceDomainV3)` and
`ContainerServiceDomainV1.Local(LocalContainerServiceDomainV1)`. Both arms carry
actual owners. A versioned startup consumes this union through the existing
credential/listener; managed V5 remains a wrapper over its existing owner.
Generic action dispatch is a separate reviewed delta after MachineAuthority
and LocalDomain factories exist. No current server field is replaced by a
string tag, and no shared server edit is authorized by this design alone.

## Concurrent release consumer changes

Release `80fdf9ff49f` changes `pane_backend.spl` native owner startup, detached
Windows process startup, and POSIX native shell selection. Its smux API moves
Host-facing imports through `std.sosix.host`. These changes must be retained
when adding the local consumer. Open Caret pane-binding/key/observer work is
separate ownership; none is evidence that the container migration is complete.

## Selected machine authority foundation

The implementation owner selected an administrator-installed machine policy
root for the initial shared-engine lane. Later per-user budgets require signed,
disjoint delegation from that same authority. This is an implementation
prerequisite, not a request field or a fallback when a policy file is missing.

Proposed factory `machine_container_authority_open_v1()` accepts no arbitrary
root, trusted SID, policy bytes, budget or provider identity from its caller.
It returns either a private `MachineContainerAuthorityV1`, an owned cleanup
turn, or pre-effect refusal. It discovers the installation location from the
OS, walks without following symlinks/reparse points, retains the exact handles,
and reads bounded fixed-child policy bytes through those handles. Windows
requires SYSTEM/Administrators ownership and no mutation rights for unrelated
principals throughout relevant ancestry; accepting the current process SID as
an owner is insufficient. Linux requires the analogous installed root-owned
protected ancestry. No POSIX mode check establishes Windows authority.

This owner admits actual machine/provider observation and exclusively opens
the existing journal/WAL storage at a fixed child. Canonical selector state
binds machine identity, provider identity, generation, configured physical
capacity and mode. The selector remains charged across ambiguous effects and
owner restart. A scope transition requires proving old workload/transport
absence, not just deleting a mode file or expiring a timestamp. Host enrollment
must reserve the same capacity domain before its existing claim publication;
local admission must reserve before provider create. Neither can redirect its
ledger to a request-selected directory.

Source inventory found reusable Simple Windows SFFI descriptor/ACL operations
in `windows_engine_pipe_abi_v1.spl` and `windows_engine_pipe_native_v1.spl`, plus
retained process-owner handle primitives. The private-root C registry's
`wp_trusted_v1` accepts the current SID and therefore cannot serve as this
factory unchanged. No installed machine-root or broker factory was located in
the inspected IO, runtime-platform and orchestration modules. Prefer a Simple
SFFI owner using OS location discovery, retained opens and existing ACL readers;
no new `rt_*` export is proposed or implemented by this lane. Any retained
native-registry bridge needed for exact journal origin requires a separate
reviewed proposal rather than a public handle or boolean assertion.

An ordinary per-user smux owner cannot mutate an administrator-only machine
ledger merely because it can read policy. The selected deployment must supply
an actual machine-authorized service owner and authenticated scoped reservation
delegation. Silent elevation and elevated local execution as a default are
excluded. Existing per-user smux token authentication does not supply that
privilege. No competing daemon, fabricated delegation or caller-chosen root is
an acceptable silent substitute. This operational authority gap blocks
switching the production caller today.

The reusable server composition already exists:
`host_primary_service_command_v5` opens `host_service_domain_open_primary_v3`
and passes the retained domain to `smux_server_serve_runtime_domain_v5`.
That server is the actual protected credential reader and sole native-thread
owner. Reuse it exactly. Missing is the independent machine-local authority
factory and typed reservation/delegation vocabulary, not the server itself.
A future tagged local-domain arm carries the actual installed-root capability;
the tag is not proof. Its startup predicate must verify the administrator
installation identity before reading local policy, then establish the shared
physical-scope ledger. The Windows lead owns the additive startup/domain/server
hooks. Current enrolled HostServiceDomainV3 cannot be relabeled to satisfy this
requirement or used to fabricate distributed signed grants.

## Independent Caret intent work

`CaretLocalContainerIntentV1` and `caret_local_container_intent_v1` preserve the
existing parsed CLI image, host executable, exact arguments, repository,
workspace, mounts, environment and network. This is unresolved app metadata.
It does not create a `LocalContainerRequestV1`, map a Windows host executable
into a guest, add implicit mounts, rewrite HOME or choose an engine. The actual
local provider must resolve the installed guest profile and independently
admit mount handles before constructing the canonical execution request.
Until that owner exists, the adapter is explicitly unconsumed groundwork and
the legacy production launch remains unchanged.
