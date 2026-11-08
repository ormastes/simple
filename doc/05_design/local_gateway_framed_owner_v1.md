# Owned local gateway frames and byte handoff

Status: implementation in progress. The later native receiver/byte-owner fixture
has one scoped PASS recorded in
`doc/09_report/local_gateway_receiver_native_20261107/README.md`. Listener,
distinct-UID sender, Simple ABI/SSpec and application integration remain
**NOT_RUN/BLOCKED**. Prior finite Unix IO and ordinary-fork evidence does not
qualify these new paths.

The gateway extends `local_ipc_v1`'s existing generation registry. A listener
owns its socket and retained no-follow parent directory. It never replaces an
existing path. Exact-inode cleanup failures retain the listener capability;
Linux close consumes its FD once even if close reports an error. Service UID
must equal the actual effective UID. Accept admits only the separately
provisioned, configured client UID, distinct from service UID, using actual
`SO_PEERCRED`. No user creation, setuid, privilege elevation, or same-UID hostile
isolation is provided. Socket mode 0666 permits distinct configured clients to
connect under a service-owned nonwritable directory; authorization occurs before
installing the accepted connection. Private authority/evidence storage stays in
a separate service-UID-only root.

## Frame and turn contract

Each connection carries one request and one response. The 16-byte prefix is
`LGW1`, little-endian u32 canonical-SDN header byte count, and little-endian u64
raw UTF-8 payload byte count. The header is at most 8192 bytes. Request payloads
are at most 2 MiB; response payloads at most 8 MiB. These transport limits can
be smaller than finite file-command limits: oversized requests are rejected,
never truncated or retried through another transport. Canonical header parsing
rejects missing, duplicate, unknown, wrongly typed or trailing fields. Prefix
and header body counts must agree before allocating the body. UTF-8 validation
preserves embedded NUL and rejects malformed byte sequences without replacement.

The client half-closes its write direction after the exact request frame. The
server requires actual EOF, rejecting trailing bytes before dispatch. Empty
reads, timeouts and poll hangup observations never substitute for EOF. Native
accepted-connection state consumes dispatch once after EOF; a copied completed
Simple reader cannot invoke a second handler. The domain must independently
verify its installed UID-to-principal/project/scope/action policy, signed grants
and retained journal records. UID or decoded request fields alone are not
application authority.

`local_gateway_turn_owned_v1` performs one zero-wait IO chunk or one bounded
domain callback per turn. It returns the latest domain owner and connection on
every path. Handler owner writeback precedes response validation, allocation and
publication. A publication failure blocks that connection without reexecuting
the callback. The response and any pending transfer descriptor remain owned.
Long provider effects must use the existing parent-owned native effect jobs;
calling a synchronous execute/wait monolith here is not supported scheduling.
The enclosing service still needs bounded connection admission, aggregate
memory accounting, reserved control capacity, and actual begin/poll/commit
composition; this per-connection turn does not claim those are complete.

## Descriptor-only transport

The Host domain retains full group/process cleanup and journal authority. An
internal response may request moving the sole unread stdout descriptor from an
exact group-stream reference into the accepted connection. The existing pipe
registry marks its source exported; later source reads fail rather than report
EOF. Previously read or exported streams cannot be exported again. The first
positive sendmsg attaches exactly one SCM_RIGHTS descriptor; partial submission
retains byte progress and never resends it. Before submission, connection
failure retains the pending FD. Connection close disposes only owned byte FDs,
never the Host process or ledger reservation.

The client's ancillary-aware reader retains at most one CLOEXEC descriptor in
the same connection registry. Ordinary request/provider reads still reject all
ancillary data. Extra or truncated ancillary messages fail and dispose newly
delivered descriptors. A completed response requires exact metadata/descriptor
presence agreement. The caller verifies `ContainerByteHandoffReceiptV1` against
its retained operation, outer request, target, nonce and gateway-incarnation
context; checksum decoding alone is insufficient. Native adoption consumes the
pending descriptor once. Capacity or validation failure leaves it owned by the
connection, and copied receipts cannot produce another endpoint.

`PipedByteEndpointV1 {generation, binding_digest}` is an explicit descriptor-only
kind in the existing 16-slot pipe registry. Its PID remains zero, and raw process
lookup excludes it. It reuses the sole existing UTF-8 reader; validate and EOF
state never call waitpid. Close affects only its exact FD and retires its native
generation. Neither EOF nor descriptor close proves process absence, group
termination, helper settlement or released capacity. Smux alone consumes its
bytes; cancellation and settlement remain authenticated Host operations.

Linux stream reservation establishes the existing verified PID/namespace origin
before creating export-eligible pipes. New transfer/endpoint operations check
that origin before allocation or owner locks and use trylock on the pipe
registry. Legacy process allocation keeps its prior locking semantics; no
general legacy post-fork safety claim is made. Windows transfer ports remain
explicitly unsupported pending its own native transport boundary.

## Verification plan

The nine pure framing cases cover both header domains, exact counts, duplicate
and unknown fields, oversized prefixes, fragmented Unicode/NUL, malformed UTF-8,
truncation and consumed-frame rejection. New listener native scenarios exercise
actual filesystem/connection ownership, zero-wait IO, close/reuse and new-port
fork refusal. Cross-UID positive scenarios require externally launched peers
under already-provisioned identities; the unprivileged fixture reports them
blocked. SCM and endpoint scenarios must use actual pipe descriptors and actual
sendmsg/recvmsg, test copied adoption/recycled close/capacity retention, and keep
full broker/resource/application authorization qualification separate. No
existing green harness is rerun as evidence for this feature.
