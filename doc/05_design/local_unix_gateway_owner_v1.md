# Shared Unix connection and byte handoff owner

The Linux host gateway and provider-private Engine HTTP calls share one bounded
generation-checked Unix connection owner. Domain and HTTP codecs stay in Simple;
the native leaf supplies descriptor ownership, nonblocking IO, kernel peer
credentials and deadline checks. It does not create a scheduler or process
supervisor. The gateway retains the returned domain owner before publishing a
response, including publication failure.

## Connection contract

`std.nogc_sync_mut.io.local_ipc_v1` owns `LocalUnixConnectionV1.token`. Native
slots validate the generation before every operation; copied stale tokens cannot
close or access reused descriptors. A global lock covers lookup/reservation only;
per-slot synchronization protects operations. Concurrent use of one connection
returns bounded busy. A maximum of 64 connections and 65536 bytes per IO call
bound storage. The caller carries one absolute monotonic deadline through all
chunks; no call accepts a horizon beyond 30000 ms.

Tokens stop at `2^60-1`; they never wrap. Socket device/inode values above that
same exact immediate-integer bound are unsupported and rejected before connect.
This prevents a heap-box allocation failure after connection creation from
truncating the returned identity. Native read receipts reserve their entire
`maximum+3` integer capacity before receive; only the reported count contains
bytes, and unused capacity is zero padding.

The first native entry opens `/proc/self/ns/pid` and requires descriptor fstat,
NSFS filesystem identity and `NS_GET_NSTYPE == CLONE_NEWPID`, then checks close
exactly once before latching the PID and namespace device/inode. A regular file
at that path cannot establish origin. Later entries compare actual path-stat
identity to the immutable pair, without requiring a fresh descriptor.
The process-origin latch is lock-free. Namespace observation
failure refuses the call. The first claimant publishes its immutable namespace
pair with release/acquire readiness; concurrent readers refuse an incomplete
publication instead of waiting or reading partial identity. PID alone is not
sufficient because separate PID namespaces can each contain PID 1. Once
the owner has been used, a fork child receives an absent native receipt before
allocation, inherited registry/slot/initialization locks or socket effects.
It cannot reset or reconstruct the registry. A fork before any owner use has an
independent zero-initialized copy and may initialize it. CLOEXEC still governs
descriptor disposal at exec; refusing a token does not itself close inherited
raw descriptors. The nullable-array facade checks absence before decoding and
returns `local_unix_native_receipt_unavailable`, retaining the supplied owner as
unconfirmed. It does not invent a precise cause: allocation failure can also
produce absence. Native foreign-process rejection performs no allocation; this
is not a claim of general Simple allocator/thread safety after fork.
An established identity observation failure or mismatch permanently quarantines
that process's registry copy. Future calls refuse before even re-observing the
namespace; restored `/proc` access cannot resurrect authority. Native fork
within an operation is unsupported. Already admitted operations retain their
bounded local scratch cleanup and unconditional mutex unlock; no uncertain
owner release or registry reset is introduced. Existing owner descriptors can
remain retained until process exit when the registry is quarantined.

Connect walks nofollow directory components from `/`, accepting root or the
configured peer UID as owner. Writable ancestors are rejected except root-owned
sticky ancestors before the final parent. The final parent must not permit
group/other writes. The socket must be an actual nofollow socket owned by the
expected peer UID. A retained parent descriptor anchors connect; before/after
device and inode observations and actual `SO_PEERCRED` bind the result. This
trusts that configured peer and administrator, not an adversarial same-UID
writer. No path creation, chmod, chown or privilege changes are performed.

Reads return bytes, EOF and errors separately. Writes return the exact accepted
byte count and never retransmit automatically. Timeout or error after a partial
Engine request leaves its operation uncertain. Close reports both descriptor
disposition and error: Linux may consume a descriptor despite a close error;
the raw descriptor must never be retried. Busy retains the owner.
Ordinary reads use `recvmsg`, reject ancillary data, and close every delivered
descriptor even on control truncation. The error still reports consumed payload
bytes. Callers must not treat ancillary rejection as absence of a request.

The admitted-write variant additionally checks a positive Unix expiry using the
real native clock immediately before each send after locks and waits. This is
local request-submission admission only. It cannot prove when the engine executes
the request, is not itself a signed grant, and does not bound process lifetime.

## Gateway and descriptor boundary

The strict Linux deployment uses separately provisioned service and client UIDs.
Kernel peer credentials must match a protected Host policy mapping UID to
principal, project, scope and allowed actions. Existing signed V2 grants remain
required. Same-UID trusted local composition is a separate weaker mode.

The intended descriptor extension transfers only one output-follow read pipe.
Host/broker retains process, cgroup, cleanup and journal authority. Smux adopts a
descriptor-only `PipedByteEndpointV1` into the existing pipe registry with a fresh
local generation. It must never invent a PID or reconstruct a group owner.
Closing that endpoint closes only byte descriptors, not processes or charges.

`ContainerByteHandoffReceiptV1` is canonical bounded SDN correlation metadata.
Its binding digest covers operation, outer request, exact target, native identity,
one-use handoff nonce, gateway startup nonce, provider generation and host source
generation. `gateway_incarnation_nonce` is a fresh cryptographic startup nonce,
not the host's continuity ID. Decoding has no authority. Authenticated connection
state and native one-use frame consumption must separately bind the descriptor;
copying a receipt must never permit another adoption or another export.

Gateway requests bound payload to 2 MiB, action to 64 bytes and operation ID to
128 bytes. Replies bound payload to 8 MiB. A stream framing implementation must
receive ancillary data on every receive, enforce exact descriptor count, reject
truncated control/data, set CLOEXEC, and dispose unexpected descriptors. Partial
publication retains the Host owner and an uncertain delivery state. Broker
diagnostics/control may never enter workload output.

## Implementation and verification status

The correlation codec and shared connection owner are the first implementation
checkpoint. Gateway listen/accept, framed SCM_RIGHTS transfer, descriptor-only
pipe adoption, authenticated Host adapter and independent-process settlement are
not implemented by the codec. They remain required before strict gateway or
end-to-end completion claims. Existing source-only in-process helper functions
remain distinct.

The six codec cases and three IO facade SSpec groups are NOT_RUN. The new native
connection fixture passed once against actual sockets and normal CoreC owners:
build 0, run 0, all 15 recorded source hashes unchanged. Its exact evidence is
`doc/06_spec/01_unit/lib/io/local_ipc_v1_native_evidence.sdn`. No separate-UID
positive result or native descriptor-transfer result is claimed. CPU use was
restricted to cores 0–4; peak artifact storage was 2,588,672 bytes. Further native
verification requires a new finite allocation. Prior passing pipe harnesses
were not repeated.

Independent review subsequently found that the first checkpoint lacked the
process-origin fence above. Its original PASS remains historical. The correction
has a separate focused `local_unix_fork_origin_v1_selfcheck.c`: both parent owner
locks and the real runtime immortal-registry spinlock are held across fork;
all five child operations must return NULL without allocation or side
effects while the parent retains its queued bytes and working connection. A
separate virgin-registry fork tests first-use behavior. This new case is NOT_RUN
pending independent source review and the allocated serialized check.
The fixture observes the actual unchanged namespace identity; namespace-changing
and PID-collision execution scenarios are NOT_RUN and require separate evidence.
It also injects one namespace-stat EIO in a virgin child's genuinely initialized
registry with a real connection. All other stat calls use the actual provider;
restoring it must not undo quarantine or change the connection's bytes/FD.

Linux contracts: [Unix sockets](https://man7.org/linux/man-pages/man7/unix.7.html)
and [recvmsg](https://man7.org/linux/man-pages/man2/recvmsg.2.html). These describe
kernel credential/descriptor mechanics, not application grant authority.
