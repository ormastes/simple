# Retained Windows Controller routing

Status: source authoring, cycle 5 of at most 6. The immutable root prerequisite
was reviewed in cycle 1; the mode separation and service-stop protocol addition
are counted in cycle 2. Tests, builds and native execution
are NOT_RUN. This is not a completed Controller service or a runtime qualification.

The selected provider is Windows Docker process through Simple Container API.
Controller and Host retain independent journals and authority. No Controller
scheduler, placement state or writer is installed into smux. Existing Linux
Controller and Host entrypoints retain their contracts.

## Existing owner reuse

`controller_local_root_v3` acquires an actual `WindowsPrivateRootV1`, its fixed
native journal child, then `distributed_operation_journal_open_windows_v3`.
Configuration and public verification policy are immutable records in that same
store. Configuration decoding is metadata only. Each current check validates the
retained root/store identity and reads the exact installed bytes through the
actual journal. Failed projection keeps its original writer for cleanup; no
decoded path or metadata constructs a native owner. Installation requires an
existing administrator-provisioned private root and publishes the two fixed
records without replacement. It does not claim to create the entire ancestor tree.

The six Controller archive/store modules gain journal-bound variants. Windows
uses the same native journal store. Linux delegates existing archive helpers
where they provide file/directory synchronization, preserving existing semantics.
Archive keys remain existing SHA256 names, within the native 128-byte component
bound. No second WAL, runtime export or journal implementation is introduced.

`host_controller_observation_v3` projects typed status from an actual retained
Host domain. Service-incarnation scope retains its real empty boot ID. Inspection
loads exact original execution packet, journal row, creation intent and observation
from that Host writer, compares all retained provenance, and invokes the common
cooperative read-only inspection API. Returned provider owners are retained before
validation errors. Inspection never recovers an old service incarnation from
metadata or grants create/start authority. Immutable inspection facts are stored
in the same journal after exact native identity and clock checks.

## Required dispatch sequence

1. Acquire protected Controller root and a genuine configured Host route.
2. Expose actual Host scope before accepting a signed dispatch packet. Opening a
   new Host after accepting a plan for a prior incarnation is not valid.
3. Reuse existing four-action signature verification, preflight guard, assignment
   admission/begin/commit and execution-ready transition oracles.
4. Retain one Host domain across validate, prepare and execute; reload Controller
   policy and clock after prepare before the execute decision.
5. Reserve each canonical continuation phase before invoking an effect. A copied
   handle may observe the canonical phase but cannot repeat a launch or close a
   sibling's in-flight ownership. Unknown outcomes never authorize retry.
6. On completion or cancellation, observe native command cleanup before closing
   Host and Controller writers. Both cleanup carriers survive independent errors.

## Selected configured-service route

The isolated candidate now includes scoped shared smux server/V5 owner/recovery edits; active worktrees remain untouched. The existing V5 Host actions retain a Host
domain, but that does not make terminal authority the owner of Controller state.
An orchestrator-owned Controller uses the existing authenticated Host route
under the distinct `retained-host-service-v1` target. It is not local-inprocess. A direct
dual-owner service instead needs the shared nonterminal service shell with a real
Windows transport. Current `HostServiceRuntimeV2` / `LocalGatewayServiceV2` use
Unix listeners and UID peer policy. The generic daemon pathname mailbox does not
provide protected Windows transport authority. A missing Windows shell producer
must be implemented explicitly, not replaced by a fake owner or a backend string.

The protected config selects the stable private V6 setup locator, its exact
canonical SDN digest, and the installed Host deployment root. No secret appears
in this configuration. The reader retains actual protected setup/root/file
capabilities and traverses the fixed Host `journal` child. It reads the exact
current `parent.lease`, positively closes that short-lived file, and selects
`host-service-ready-v6/<lease-digest>.sdn`. This immutable record binds the setup
digest, Host authority/lease digests, actual endpoint, diagnostic PID and fresh
service incarnation. Generic V2 initial/ready parsing stays unchanged and cannot
accept these records. Setup custody and Host writer custody are separate genuine
owners; neither pathname nor an asserted same-directory relationship replaces them.

Controller cleanup consumes its exchange/socket before the borrowed credential
reader and Controller root. It never treats
disconnect or accepted cancel as remote Host command cleanup or closes the
independently owned Host service writer. Exact operation/scope/request/incarnation
checks must occur atomically in the Host owner before progress/cancel. The actual
Controller consumer, signed continuation and cleanup integration remain outstanding.

## Ownership and evidence

Astra owns the new Controller configuration/root and Host observation facade.
The smaller Controller storage worker owns six archive/store modules plus their
specifications. The separate pre-start hook owns five existing Host files; this
lane does not overwrite them. All work is isolated under `/tmp`; no worktree,
index, branch, runtime, deployment, key-store or stopped SSH consumer is modified.
An independent Astra review is required before accepting a coherent source slice.

Restart does not rotate the setup key or overwrite ready records. The existing
Host journal open replaces its own lease; no new selector or writer is added.
Windows close leaves that lease, so selection alone is not liveness. Failed
startup can leave a new lease with no ready record: the reader reports unavailable
and never falls back. The native read sharing mode can make a concurrent lease
replacement fail; actual read cleanup and Host quarantine remain retained, with
no transparent restart or power-loss continuity claim. Every ordinary MAC use
and final result consumption checks the selected lease. Drift during final stop
reply delivery is Unknown; confirmed Host-close facts stay internal and the
client never automatically resends or reconnects to repeat the effect.

The integrated verifier additionally depends on repairing the existing native
`rt_black_box` fallback's shared volatile sink. The assigned runtime change uses
function-local volatile storage in the two fallback branches and preserves the
GNU assembly/ABI. Authored request/reply MAC regressions reject all 64 individual
valid-hex mutations. Source review, a fixed-width loop, or an OR guard does not
establish timing behavior or repair a still-installed old runtime. Native
concurrency, timing and live authenticated routing remain NOT_RUN.


## Authenticated mode and current implementation boundary

The reviewed architecture now selects explicit **V6-only Host transport**.
Default V5 remains unchanged. V6 never accepts a bearer request or falls back to
V5. Its fresh OS-generated secret resides only in the protected, versioned
private setup record. The versioned ready record contains the setup digest,
publication UID, endpoint, diagnostic PID and service incarnation, but no
secret. Both formats are incompatible with legacy fixed-field extraction.
Protected setup provenance trusts the existing administrator boundary; it is
not an attestation against administrator tampering. This credential is separate
from SSH keys and shared server identity references.

Each TCP connection has one server-generated challenge. The canonical IO owner
consumes it before request validation and exposes a one-use verified-request
capability for immediate Host dispatch. The client authenticates the challenge
before transmitting a command, retains exact partial-write offsets, records
unknown disposition before its first request write, and never automatically
resends an effect. Both directions bind exact canonical request bytes through
the outer command digest. SMUX/1 declared response lengths are consumed without
waiting for EOF; handshake deadlines do not reset on progress.

Service stop is an authenticated, exact-incarnation and exact-scope action.
After existing stop guards pass, the server must enter a sticky quiescing state
before any Host close. It stops accepting or dispatching further requests,
retains the auth reader while signing and draining the stop response, and only
then closes the socket/listener and credential capabilities. A successful stop
response certifies Host obligations closed, not the later transport or
credential cleanup. Partial close never returns the instance to ready service.

Controller execution remains finite and orchestrator-owned: retained Controller
root and reader perform status, validation, preparation and execution against
one persistent Host instance. A pending or lost execute reply is not permission
to resend; a later invocation uses the exact operation/digest inspection or
progress route. Controller and Host journals remain independent.

At this source-authoring point the root/observation prerequisite has independent
source acceptance, and the IO connection/client owners are authored but not yet
reviewed or consumed by the complete app route. All runtime, native, deployed
service and end-to-end scenarios remain NOT_RUN. The required interactive
AgentSession terminal bind/attachment is still a separate missing integration;
it must later use the same retained Host owner and authenticated credential
mode. No noninteractive App5 substitution or second physical-budget owner is
claimed. The dedicated nonterminal service shell remains a deployment gap.

## Deployment boundary

This implementation is a local Windows Controller-to-Host route. The client needs actual protected filesystem access to the Host deployment journal and pinned private setup record. A TCP tunnel alone does not supply those capabilities. The Controller writer and its assignment/state journal remain on the Controller machine; a future cross-host transport must use a Host-side authenticated bridge and observations, not move or reopen the Controller journal on the Host. The IO exchange remains the transport seam. Held SSH consumer work is unchanged.

The V6 Host continuation extraction preserves the sole retained Domain in the V5 service owner. The extracted continuation holds Host execution, inspection and publication state, but no duplicate Domain or journal. The V5 file is 973 lines, compared with its inherited 939-line baseline; this existing size debt is recorded rather than broadening this change into unrelated terminal ownership.

## Source evidence and current review boundary

The actual OS-entropy publisher is reachable through `host-auth-setup SETUP_PATH`; the application accepts no caller secret and cannot convert an old bearer. Its result carries public UID/digest and historical publication status, while unresolved native cleanup remains an opaque process-local reply field consumed by the canonical finalizer. This MAC setup is not the shared SSH identity store and is not SCV bearer-token reuse.

The genuine system specimens are separate: direct live protected-reader/challenge/status/cleanup, and the actual installed Controller CLI/status/typed observation/archive/finalizer route. Both require dedicated genuine Windows configuration and fail on missing fixtures; both are AUTHORED_NOT_RUN. Early refusal specimens use the real dispatcher and never fabricate an opaque native owner.

Runtime primitive source dependency is merged #9579, commit `9bb319f981bfed6f6517ea790dbd04532d13f0c3`. It removes the MSVC/generic shared volatile sink from `rt_black_box`; concurrent native identity and optimizer/timing qualification remain NOT_RUN. Production MAC equal/mutated-tag regression scenarios are authored in this package and unexecuted.

The first actual server composition review found a missing monotonic-clock import after extraction and three unit-result/bool-result mismatches in native origin guards. The consolidated cycle 3 correction restores the existing import and explicitly propagates each native guard before returning `Ok(true)`. No native guard or origin check is removed or reordered. Tests/compiler execution remain NOT_RUN.

## Canonical Controller continuation correction

Integrated source review identified a stale-copy lifetime error: after an earlier value-copy advanced from exchange E1 to E2, closing the earlier copy could close the shared reader and Controller root before E2. Cycle 4 replaces copied resource custody with a guarded canonical continuation. Opaque handles identify one current state by never-reused identity and revision. The exact revision is reserved before effects; returned resources replace canonical custody before errors are classified. A stale call performs no effect and returns explicit refusal plus the current handle for deliberate adoption. It must not poison the current operation outcome.

Pre-registration origin/capacity refusal retains the actual supplied root in a private cleanup-only unregistered dispatch arm. That arm can never launch; after a valid native origin check it compares actual native journal identity against every active canonical dispatch before cleanup. A duplicate returns the current handle with refusal and no effects; an indeterminate identity stays retained. The default `root_cleanup` turn field remains nil for these cases, preventing a later standalone finalizer from closing a still-adopted root alias. Registered continuations keep root/reader/exchange together; no duplicate journal or cleanup registry is introduced. The existing Root gains only a guarded same-native-journal-identity comparator, with no WAL/policy refresh or liveness claim. Finite cleanup remains reachable even on revision exhaustion. These are source invariants requiring exact independent review and genuine fixture qualification, not a latest-return documentation workaround.

Cycle accounting: the first canonical implementation was cycle 4. Its lead source review found a new unit-to-bool native guard adapter error and insufficient reporting of unregistered consumed-but-unconfirmed Root cleanup. Correcting those together with the reported genuine-fixture carrier/polling issues is cycle 5, even though independent final review has not yet run. The initial draft remains immutable evidence. One correction cycle remains; artifact names or review ownership do not reset this limit.
