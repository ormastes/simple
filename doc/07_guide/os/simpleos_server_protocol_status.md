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
channel admission. Its SFTP subsystem currently proves authenticated SFTP v3
negotiation and bounded framing only. It rejects duplicate initialization and
all filesystem operations because no VFS capability is injected. Do not
advertise file transfer through SFTP until that owner and a live OpenSSH SFTP
transcript exist. The legacy combined-server QEMU checker is not current
acceptance evidence because it builds with the Rust seed and probes a hardcoded
password; see the tracked bug records.

Current source-only checks cannot replace live evidence. Resume focused checks
after deploying an admitted Stage 4 `bin/simple`; then run the canonical HTTP
loopback specs and the SSH QEMU specs from their in-file operator instructions.
The production servers also do not yet publish the architecture's canonical
capability manifest; that wiring remains tracked and must precede any unified
protocol advertisement.
