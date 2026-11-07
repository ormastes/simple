# Canonical terminal reference state

Source: `test/01_unit/os/apps/smux/runtime_terminal_ref_spec.spl`.
Status: **AUTHORED_UNRUN**. This companion is authored, not generated evidence.
Native builds, test execution and docgen remain blocked pending admitted
daemon/provider dependencies and a root-authorized build slot.

These fourteen scenarios use synthetic reference/owner values exclusively for pure state
operations. They never invoke native process methods on those references and
do not prove a live stream, authenticated binding, provider attachment or agent
readiness.

1. Preserve all four authority fields (PID, generation, group root and group
   identity), terminal rendering provenance, EOF and retained
   read failure through focus, input, geometry and response-state clones.
2. Distinguish a reused diagnostic PID by registry generation; advance child
   incarnation for a changed reference, preserve incarnation for the same one,
   and clear reference ownership in the post-close state projection.
3. Reject changed group root or group identity even when PID and generation
   match; use the canonical owner's shared equality helper and advance child
   incarnation for either authority change.
4. Include canonical identity in configuration comparison even if a diagnostic
   PID or stale incarnation counter did not change.
5. Refuse text, command, paste and literal-input admission before queue/native
   effects. Reject native geometry claims through both pure capability and
   direct changed-geometry transaction checks, and replacement configured launches
   while the canonical owner remains attached.
6. Reject split rollback after a canonical generation, group-root or group-identity
   change before any native
   geometry compensation.
7. Preserve the complete owned transfer and cleaned-awaiting-release flag across
   every clone; generic child/PTY/ref replacement must not erase the owner.
8. Detect a changed cleanup owner even when the canonical reference is identical.
   Include that bundle and the cleanup phase in configuration identity.
9. With helper cleanup already marked complete, retain all owner/ref metadata,
   refuse generic reset/removal/replacement and perform no further native
   cleanup or stream operations. This models the pending host-release phase;
   it does not simulate a successful native cleanup.
10. Reject budget-bearing group references on the legacy bare adoption path
    before native validation, preserving the requirement for a complete transfer.
11. Refuse split rollback when full cleanup authority or the one-shot cleanup
    flag changed, before any geometry compensation.
12. Refuse server stop while a pane retains an owned bundle, bare canonical
    reference or cleaned-awaiting-release flag. The refusal cannot classify as
    a successful legacy stop response; the empty-owner reply remains unchanged.
13. Exercise authentication and empty-owner stop through the actual production
    dispatcher in an isolated spec process, without mutating its global owner
    to inject synthetic references. No socket/process acceptance is claimed.
14. Reject literal/text/command/paste input before queue or native effects even
    for inconsistent pending-release state with no bundle/ref and child PID -1.

The owned fixtures use actual `GroupProcessStreamRequestV2`,
`GroupProcessStreamLaunchV2`, `GroupProcessStreamOwnerV2` and
`PipedProcessOwnedTransferV2` layouts, with synthetic paths and identities for
storage/comparison only. No native launch, registry validation, cleanup or effect is
invoked on those fabricated owners. The cleaned-state close/poll checks take
only their production early-refusal paths.

`PipedProcessRefV1` is process-local registry-lifetime authority. Its PID,
generation, group root and group identity cannot be restored or deserialized as authority after
restart. Recovery must acquire a fresh reference from the issuing owner.

Actual terminal adoption requires a validated owner-issued registry reference, exact target
revision/incarnation fencing and exclusive reader transfer. The existing pane
reader drains through explicit EOF; neither validation nor EOF proves process
liveness or exit. POSIX liveness is explicitly unsupported. Deferred reads are
not EOF, and read errors
retain cleanup authority. Successful adoption means only that smux owns the
output-only helper. It does not prove the engine attached. Input, native
geometry and interactive operation remain unsupported for this transport.

The new trusted owned adoption route retains the full cleanup owner together
with its stream reference. Successful helper cleanup sets
`helper_cleaned_awaiting_release`, retains the pane and bundle, and stops further
stream operations. It is not host budget release. Generic close remains pending
until a future verified host reap/release acknowledgement, whose API is not
implemented here. Repeated successful cleanup is not assumed idempotent.
Reset pre-scans the entire service and refuses owned or pending-release state
before any native effect. No fake acknowledgement or successful bind route is
provided by these changes.
Authenticated stop refuses before returning its accepted stop response whenever
the current pane snapshot retains typed cleanup authority. The server loop thus
keeps serving instead of exiting after a reset refusal. Future configured binding
context must additionally account for provider `CleanupRequired` owners that
have not yet transferred a reference into any pane; that context is not installed
by this slice and remains a required integration gap.

Live EOF/drain, stale-generation registry rejection, close failure/retry,
provider output, authenticated positive binding and restart reconciliation
still require real admitted integration tests. No passing claim is made here.
Daemon owned-transfer helper imports are an external dependency; no local stub
substitutes for their implementation or qualification.
