# Canonical terminal reference state

Source: `test/01_unit/os/apps/smux/runtime_terminal_ref_spec.spl`.
Status: **AUTHORED_UNRUN**. This companion is authored, not generated evidence.
Native builds, test execution and docgen remain blocked pending admitted
daemon/provider dependencies and a root-authorized build slot.

These five scenarios use synthetic reference values exclusively for pure state
operations. They never invoke native process methods on those references and
do not prove a live stream, authenticated binding, provider attachment or agent
readiness.

1. Preserve canonical reference, terminal rendering provenance, EOF and retained
   read failure through focus, input, geometry and response-state clones.
2. Distinguish a reused diagnostic PID by registry generation; advance child
   incarnation for a changed reference, preserve incarnation for the same one,
   and clear reference ownership in the post-close state projection.
3. Include canonical identity in configuration comparison even if a diagnostic
   PID or stale incarnation counter did not change.
4. Refuse text, command, paste and literal-input admission before queue/native
   effects. Reject native geometry claims through both pure capability and
   direct changed-geometry transaction checks, and replacement configured launches
   while the canonical owner remains attached.
5. Reject split rollback after a canonical generation change before any native
   geometry compensation.

`PipedProcessRefV1` is process-local registry-lifetime authority. PID and
generation fields cannot be restored or deserialized as authority after
restart. Recovery must acquire a fresh reference from the issuing owner.

Actual terminal adoption requires a validated owner-issued registry reference, exact target
revision/incarnation fencing and exclusive reader transfer. The existing pane
reader drains through explicit EOF; neither validation nor EOF proves process
liveness or exit. POSIX liveness is explicitly unsupported. Deferred reads are
not EOF, and read errors
retain cleanup authority. Successful adoption means only that smux owns the
output-only helper. It does not prove the engine attached. Input, native
geometry and interactive operation remain unsupported for this transport.

Live EOF/drain, stale-generation registry rejection, close failure/retry,
provider output, authenticated positive binding and restart reconciliation
still require real admitted integration tests. No passing claim is made here.
