# SimpleOS server protocol status

The production hosted HTTP owner is `src/lib/nogc_async_mut/http_server/`.
Its TCP/TLS ALPN boundary accepts only absent/`http/1.1` and exact `h2`.
Unknown identifiers, including `h3`, are closed without HTTP/1.1 downgrade.
HTTP/3, QUIC, and WebTransport are unavailable until the end-to-end owners
required by `doc/04_architecture/simpleos_complete_os_hardening.md` exist.

The browser-facing Simple Web owners under `src/app/ui.web/` provide the
bounded HTTP/1.1 WebSocket upgrade path. This does not imply that the generic
HTTP server automatically upgrades arbitrary routes.

The SimpleOS SSH daemon uses configured public-key identities and bounded
channel admission. Its SFTP v3 owner negotiates and frames requests, but every
filesystem operation fails closed with `SSH_FX_OP_UNSUPPORTED`: the canonical
VFS does not yet expose a per-principal revocable capability with atomic
beneath/no-follow lookup or non-materializing paged iteration, and SFTP must not
emulate those guarantees with stat-then-open or slicing a full listing. This is
source and host-fixture capability evidence only; do not advertise live file
transfer until those controls and a current OpenSSH SFTP transcript exist. The legacy combined-server QEMU checker is not current
acceptance evidence because it builds with the Rust seed and probes a hardcoded
password; see the tracked bug records.

Current source-only checks cannot replace live evidence. Resume focused checks
after deploying an admitted Stage 4 `bin/simple`; then run the canonical HTTP
loopback specs and the SSH QEMU specs from their in-file operator instructions.
Production startup and negotiation now share
`std.common.contracts.execution.simpleos_server_protocol_capabilities`. HTTP
publishes manifests only after ready-generation loopback evidence; TLS ALPN
uses the same exact H1/H2 reachability predicate. SSH publishes only after the
listener, configured public-key identity, and host-key policy are ready.
SFTP remains unpublished even after authenticated subsystem framing because no
per-principal atomic VFS capability is injected. HTTP/3, QUIC,
WebTransport, generic-server WebSocket, and unknown identifiers remain absent
and fail closed.

SSH filesystem exec is currently implemented only for x86_64 and RISC-V 64.
The x86_32, ARM64, ARM32, and RISC-V 32 daemon variants fail closed with exit
status `126` (accepted command, target launcher unavailable); they never report
exit `0` without running a program. The result has empty channel output and
`truncated=false`, preserving the existing unsupported-target API. Exit `127`
continues to mean command/PATH resolution failure on an
implemented launcher. This source contract does not advertise target-native or
QEMU execution for the unsupported variants.
# Filesystem-launched database provisioning

The `/SERVERS.ELF` database listener is an adapter to `DbdServer`, not a second
database implementation. It reads `/SYS/SRVDB.KEY`, `/SYS/SRVDB.CRT`, and
`/SYS/SRVDB.PK8` as bounded owned byte buffers, invokes
`DbdServer.provision_service`, and verifies zeroization of every source buffer
before DBFS recovery. The paths are configuration locations, never embedded
credential values.

The image owner requires all three files together. It bounds each regular-file
read before allocation, validates DER X.509 and Ed25519 PKCS#8 types plus public
key equality, stages an adjacent `/SYS/SRVDB.MAN` hash manifest, and compares
the three source hashes again after construction. There is no embedded key,
certificate, development fallback, or partial server-image mode.

Startup additionally requires the mounted VFS owner to attest DBFS root,
durable file sync, and transactional namespace replacement. A missing bit is a
hard startup failure. Operators should never place secrets in command-line
arguments; filesystem launch admission rejects all DBD arguments.
