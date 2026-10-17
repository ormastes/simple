# Local SMUX Windows findings

The hosted entry is `src/app/hosted_apps/smux_client.spl`; production state
belongs to `src/os/apps/smux/api.spl` and `service.spl`. The old stdin owner
destroys children at EOF. Attachment metadata alone does not implement an
independent server. The old system spec includes local replicas and cannot
establish production API behavior.

The separate pure `mux_model.spl` previously had no production consumer. Its
named geometry now shares `mux_rects.spl` with production layout selection;
service and protocol tests must remain distinct from pure-model tests.

Existing `std.nogc_sync_mut.io.tcp` supports listener timeouts, bounded reads,
raw nonblocking mode and streams. Reads currently conflate WouldBlock with
other errors, so the owner retains partial input until an absolute deadline.
Writes can be partial and need a retained offset. The core-C Windows runtime
still contains TCP failure stubs; the Rust lane is a different provider.

PTY output can be drained with zero-timeout reads. PTY writes and terminal
query replies can block in the existing native provider. No live child resize
provider is currently connected to SMUX. Therefore read-loop bounds and
VT-grid changes cannot certify input fairness or ResizePseudoConsole.

Exact Windows producer hashes, receipts, finite diagnostic attempts and
remaining HIR/link uncertainty are retained in
`doc/09_report/smux_windows_build_2026-10-16.md`. No qualified general SSpec
runtime was available for these feature changes.
