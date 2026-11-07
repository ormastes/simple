# Canonical local Unix listener and zero-wait owner

Status: SOURCE ONLY / NOT_RUN. The earlier finite-I/O/fork repair checkpoint is
separate; no old native check is rerun or claimed for this new listener slice.

The new Simple spec has four invalid-input/retention cases at
`test/01_unit/lib/io/local_ipc_listener_v1_spec.spl`. Actual native mechanisms are
in `src/runtime/test/local_unix_listener_now_v1_selfcheck.c`, which includes the
actual CoreC runtime allocator once. A future build must omit a second
runtime_native.c translation unit; no fake allocator/provider is used.

Listener and byte connection roles share the existing bounded 64-slot registry,
positive immediate generation tokens, per-slot operation locks and process-origin
PID/actual namespace/quarantine profile. Every new port checks origin before
allocation. Connection ports reject listener roles, and listener close rejects
connection roles. Public descriptors remain opaque and process-local.

Listen requires actual service UID equal to geteuid, a protected no-follow
retained parent and backlog 1..128. It never unlinks/replaces an existing entry.
It reserves a cleanup-bearing token before bind, sets the new socket mode to
0666 without changing process-global umask and publishes listening success only
after exact node identity/mode checks. The configured same-UID admin namespace
remains trusted; this is not hostile-same-UID isolation. Bind followed by
unobservable node identity conservatively retains cleanup authority.

Accept is nonblocking, requires a configured client UID distinct from the service
UID, and checks actual accepted SO_PEERCRED before registry installation. Peer
rechecks actual SO_PEERCRED under the same token lock. Peer device/inode denotes
the connected target path on a client and the captured listener path on an
accepted connection; it is not a client pathname or process-liveness proof.

Poll uses zero wait. Now read/write use the same recvmsg/partial-send cores,
report would-block explicitly and never treat it as EOF or retry a request.
Unexpected ancillary rights are rejected/disposed by that shared reader.
Write-half shutdown retains the read half/owner, repeats idempotently and prevents
later writes. The peer must observe actual EOF; timeout is not EOF.

One-use request claim requires an accepted connection and EOF actually observed
by the shared reader, then binds one 64-lowercase-hex request ID in its slot.
Copied completed frames cannot claim twice. This phase is not grant validation,
callback execution or another journal. No callback/effect runs under its lock.

Listener close consumes its descriptor once, then conditionally unlinks only the
captured node under its retained parent. Failure or identity substitution retains
the listener with fd=-1 for pathname-only cleanup retry, never retrying a reused
raw fd. Missing owned pathname is already absent; a replacement is not removed.

The NEW native fixture covers existing-file preservation, explicit mode, role
refusal, no-wait empty accept, actual wrong-UID refusal, connected peer/poll/bytes,
half-close/read-half preservation, thirteen-new-port fork refusal with held actual
allocator/owner gates and retained exact-inode cleanup with reused-fd safety.
The single-process fixture reports distinct-UID accepted/EOF/duplicate-claim
positive testing as BLOCKED. The separate authored protocol fixture
`src/runtime/test/local_unix_external_peer_v1_selfcheck.c` has server/client modes
that MUST be launched externally under two already-provisioned distinct UIDs.
It never creates users, changes identity, elevates privileges or launches a peer.
The service parent must already be provisioned as service-owned, traversable by
the client and not group/other writable. The listener creates only its explicit
0666 socket leaf under that parent.

External protocol (NOT_RUN): start `--server SOCKET_PATH EXPECTED_CLIENT_UID`
under the existing service identity, observe READY, then independently start
`--client SOCKET_PATH EXPECTED_SERVICE_UID` under the existing client identity.
Both expected IDs must differ from their process's actual geteuid. The client
uses the canonical connection owner to send one byte and half-close. The server
checks actual kernel peer credentials, requires observed EOF, claims one request
and rejects both identical and different-ID second claims. Test-only raw poll
waits for readiness without adding a second reader. No namespace setup, mocked
accepted flag or synthetic UID assertion substitutes for this evidence.
SCM frame transport, complete gateway, production daemon signing and all new
execution evidence remain NOT_RUN.

## Explicit descriptor handoff (SOURCE ONLY / NOT_RUN)

The same connection slot now retains one pending FD and phase 0 none, 1 staged,
2 sent, 3 received, 4 adopted. Stage requires an accepted, one-use-claimed request
before any positive response bytes, and moves the exact unread stdout through
the canonical process owner's private bridge. Its first positive sendmsg carries
one SCM_RIGHTS FD, records exact accepted bytes and closes the local transfer FD
once. EAGAIN/error retains the staged FD; later writes never send it twice.
Close disposes only pending transport descriptors and claims no helper lifecycle.

Only a connected, write-half-shut client may use explicit handoff receive. It
shares the ordinary recvmsg reader; ordinary reads still reject/dispose rights.
At most one FD can ever be received. Extra or truncated control disposes every
new FD while preserving the original pending owner and consumed payload count.
EOF leaves the pending descriptor retained. State observation exposes no FD.
Adoption requires actual EOF and delegates to the existing descriptor-only pipe
registry. Capacity failure retains pending ownership. The first adoption attempt
latches its exact 64-lowercase-hex binding; a retry with another binding is denied
without relabeling that FD. Success consumes once; copied adoption cannot repeat.
Bindings alone are correlation data, never host policy or authenticated evidence.

`src/runtime/test/local_unix_scm_receive_v1_selfcheck.c` is a new actual mechanism
fixture: canonical connected client, test-owned raw peer/real pipes, SCM receive,
EAGAIN pending retention, extra and 32-right truncation disposal, EOF, actual shared
16-slot capacity failure, changed-binding retry refusal, original-binding success,
copied adoption denial, byte EOF and queued-FD disposal. It links actual
runtime_process.c and normal CoreC owners. No accepted flag, helper PID or terminal
proof is fabricated. All cases are currently NOT_RUN.

Stage/send integration remains NOT_RUN until an actual separately provisioned
client UID and real admitted group helper are available in the server process.
Use the full actual Ready/CleanupRequired owner and unread reference; do not
serialize a live lease or manufacture private registry phases. After real request
EOF and claim, stage before response prefix. A one-shot sendmsg EAGAIN injection
may test retention while delegating all other syscalls to the actual provider;
then actual positive sendmsg must deliver exactly one descriptor, including across
partial writes. Verify source replay refusal and descriptor disposal on connection
failure without deriving any helper resource release from byte EOF. Application
policy/receipt verification and independent broker proof remain required.
