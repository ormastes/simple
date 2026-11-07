# Same-slot grouped input revision barrier V1

Status: implemented source under review; all tests NOT_RUN. No native build,
provider adoption, performance or full daemon qualification is claimed.

The canonical `s_procs[16]` slot retains control policy and actual last-write
receipt. It introduces no registry, supervisor, reader or application grant
ledger. Only a full grouped `PipedProcessRefV1` selects the existing generation,
root, identity, PID and published phase under `s_proc_lock`. Controlled mode is
permanent until slot retirement. Install/revoke and the actual write share that
gate, so successful revoke acknowledges that no later write under that revision
can cross the gate. It does not retract previously accepted bytes.

## Interfaces

Vocabulary lives in `std.common.process.input_control_v1`; the additive owner
facade is `std.nogc_sync_mut.io.process_input_control_v1`, importing only the
existing reference type from process_ops. Mutations
`process_input_control_{enable,install,revoke}_ref_v1` return `Result<(),text>`.
`process_input_control_state_ref_v1` returns actual validated slot state.
`process_write_stdin_some_controlled_ref_v1` returns ProcessInputWriteTurnV1
with the original reference, disposition, requested attempt, accepted byte count
and diagnostic on every path. This is process-local metadata, not wire authority.

Install requires a 64-lowerhex target and nonce, positive revision and absolute
monotonic-nanosecond expiry. Exact active install is idempotent; lower/conflicting
or revoked same revision cannot resurrect. A higher revision resets the current
attempt sequence only. Revoke matches target, nonce and revision exactly, and
repeated exact revoke remains idempotent. Deadlines are actual monotonic checks,
not a production caller clock. Every native output integer is in signed61bit
immediate range; revision, expiry and attempt inputs outside that range reject
before effects, avoiding postwrite integer boxing/allocation.

Enable blocks all existing POSIX slot-writer routes, including raw PID, ref,
owned-ref and renderer/VT adapters. Existing raw/ref selectors already deny
group tickets. The grouped legacy writer additionally checks canonical process
origin before its lock: a pre-enable fork copy cannot bypass a later parent
barrier through its inherited descriptor. Unrelated raw APIs and Windows legacy
behavior remain outside this change. New grouped-control ports are Linux-only;
non-Linux returns explicit unsupported.

## Native receipts and write semantics

Exactly five OS leaves are defined in runtime_process.c and declared in
runtime.h: rt_process_input_enable_v1, rt_process_input_install_v1,
rt_process_input_revoke_v1, rt_process_input_state_v1 and
rt_process_input_write_some_v1. They use the existing reviewed C-only owner
policy; no census extractor, baseline or enforcement changes.

Every leaf checks canonical origin before allocator or owner gate, preallocates
and prefills its nullable array receipt, then uses nonblocking trylock. Native
NULL is honest receipt-unavailable, never zero-effect proof for a write.
Mutation receipts are `[status,applied]`. Write receipts are
`[status,disposition,attempt,accepted_bytes]`, where disposition0=Rejected,
1=Recorded and2=Unknown. State is exactly268words:
`[status,controlled,active,revision,expires,current_sequence,last_sequence,
last_accepted,last_status,last_disposition,last_revision,last_expires]` followed
by four64-byte ASCII digests: active target, active nonce, last target, last nonce.
The facade validates presence, lengths, integer/digest ranges and cross-field
relations before exposing state. Query does not mint authority; recovery must
compare last revision, target, nonce, expiry and attempt exactly.

A write requires active exact metadata and exactly current_sequence+1, bounded
counted-byte offset and maximum1..4096. Actual monotonic expiry is checked after
signal setup immediately before sequence consumption and one nonblocking write.
Every consumed attempt, including EAGAIN/zero and EPIPE, is recorded. Duplicate or
other rejected preflight never overwrites the last consumed result. Last receipt
and its identity survive higher install until the next consumed attempt. Native
attempt sequence is independent of any common frame sequence.

SIGPIPE is blocked on the current thread for the syscall. EPIPE drains at most
one zero-time sigtimedwait; no blocking sigwait enters the new path. An uncertain
drain keeps SIGPIPE blocked and reports signal-state error rather than unmasking
a possibly fatal pending signal. Mask restoration failures remain visible.
Actual known syscall count remains Recorded with its diagnostic even after a
signal-state failure. Unknown uses accepted=-1, never a fabricated zero prefix.
Nullable/malformed facade receipt returns Unknown while retaining the reference;
there is no automatic retry. Recorded count is bounded by the actual requested
remaining byte range, not merely4096. Payload can contain NUL; lengths and
progress are bytes.

## Verification and limits

Three SSpec cases cover invalid-reference preeffect rejection and retained turn
identity. The new native fixture uses actual reserve/bind/claim/publication,
real test-owned pipe endpoints and actual forked helper PID, explicitly
transport-only. It covers old-writer denial, copied pre-enable writer refusal
with held/unlocked gates, exact install/idempotency, real prefix delivery,
duplicate rejection, actual saturation/EAGAIN, revoke nonresurrection,
higher-revision retained receipt, metadata/range rejection, EPIPE, expiry and
stale generation after slot reuse. TEST harness teardown never fabricates a
broker terminal marker or production cleanup success.

All cases are NOT_RUN. Full Simple facade decoding under actual allocation or
receipt corruption failure, concurrent revoke/write stress, signal restoration
fault injection, live cgroup/broker lifecycle and application input grant/revision
integration remain unqualified. The new gate does not make unrelated legacy
SIGPIPE helpers bounded, guarantee application execution, retract written bytes,
or serialize a live capability for recovery.
