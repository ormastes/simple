# Pinned Host service peer composition

The trusted local administrator supplies the protected Host root and exact
transport-policy SHA-256 to `host_service_gateway_open_v2`. Neither input comes
from a gateway request. The fixed child is
`host-service-peer-policy-v2.sdn`. Its pin is distinct from the SDK grant policy,
enrollment binding and exec-control identity pins.

The pure canonical SDN codec accepts 1–64 unique integer UIDs, each with one
explicit principal, project, exact service scope and 1–8 distinct known actions.
There is no wildcard, default, duplicate UID or ignored field. UID bounds are
0 through 4294967294. The policy source is bounded to 64 KiB and depth five.
The codec opens no file; its data is not authority by itself.

The actual loader explicitly requires Linux. It opens the fixed file relative
to a trusted retained directory, requires a regular private owner/0600 file,
reads bounded bytes, validates stable descriptor identity and exact pin, then
decodes the canonical policy. The same retained FD's native security metadata
supplies the observed service EUID. Every configured client UID must differ
from it. Parent/file close failures remain explicit consumed-close errors;
there is no raw-FD retry, mode repair, shell or ABI declaration.

The loaded snapshot retains the protected root, transport digest and observed
service UID. Gateway open then opens the actual owned Host domain. Every policy
scope must match both the opened domain and its configured service scope. A
post-open mismatch closes the exact owner: only empty error, nil cleanup,
`closed=true` and canonical `Released` become a simple rejection. Every other
close turn, including nil-cleanup consumed errors, remains
`CloseCleanupRequired`. Open cleanup capabilities are forwarded separately.

The snapshot is immutable for the process lifetime. Policy changes require a
controlled stop/reopen with a newly approved bootstrap pin. Requests cannot
select a policy path, pin, root, UID or reload operation. Callback composition
also rejects a snapshot paired with a different root. The later actual native
listener independently verifies the observed service UID remains current and
that the selected client UID is distinct.

The SDK constructs `LocalGatewayRequestV1` only after native kernel-peer,
framing and one-use connection checks. The Host callback maps that actual UID
and exact action, then supplies a trusted mapped context to the domain. Status
and validate are explicit allowed reads; they do not claim execution authority.
The policy table does not implement a multi-UID listener: the current SDK
listener still accepts one configured client UID. Listener selection, native
loop ownership and descriptor handoff remain the daemon lane's responsibility.

Prepare checks its already decoded original operation principal/project and
reservation service scope before SDK authorization. Budget checks its same
decoded proof operation, original Host operation, controller operation, budget
scope and parent scope. Existing shared matchers already require those three
operation subjects to agree; an issuer identity is a separate concept. No
implicit controller delegation is added. The gateway decodes neither packet.
Prepare retains its existing core reply decode; no third decode is introduced.
The prior trusted in-process domain turn remains available separately.

The callback retains the complete returned domain owner before constructing the
SDK response. `host_service_gateway_turn_v2` invokes the actual generic
`local_gateway_turn_owned_v1`, whose owner survives response validation/send
failures. None of the four effect routes is accepted or queued here. They do
not invoke synchronous execute, inspect, wait or cleanup on the control loop.
No listener, PTY reader, native effect protocol, queue or second journal is added.

`host_service_gateway_classify_v2(owner, incoming)` supplies scheduling metadata
only after one shared mapped-request validator checks root provenance, actual
SDK peer UID distinct from service UID, unique UID/action rule, exact mapped
scope and request shape, in that order. The callback invokes that same validator
again at dispatch. The mapped-domain scope condition is extracted unchanged
into `host_service_mapped_peer_error_v2`; trusted in-process behavior remains.

Only an allowed `host-status` request returns `ControlRead`. Allowed validate,
prepare and parent-budget requests return `Work`. Every effect action returns
dispatch-required even when present in the policy. The classifier decodes no
signed packet, verifies no SDK proof, reads no journal/provider and publishes
no response. A work class is not admission: the callback still performs its
same-decoded subject checks and current SDK authorization. A previous class
cannot authorize changed peer metadata or skip callback revalidation.

The daemon owns actual receive-ready/dispatch/publication splitting and bounded
scheduling. It must classify only metadata produced after real EOF and kernel
peer checks, then retain the native one-use claim at dispatch. This delta adds
no dependency on an unpublished SDK split and no loop/listener extension.

Startup reads at most one 64-KiB policy. Callback mapping scans at most 64 rules
and eight actions, with no policy file reread/hot reload. Actual native startup,
socket latency, send-failure retention, fault-injected cleanup states and control
responsiveness are unqualified. Twenty-three authored scenarios are **NOT_RUN**;
static/source review does not establish those runtime properties.
