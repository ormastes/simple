# SimpleOS tool output capture

Initial execution qualification is x86_64 only and remains TEST_BLOCKED until
an admitted compiler builds and executes the real tool probe. Authored unit
specs and source review do not admit runtime behavior on any architecture.

The file-write syscall derives the actual caller from `Scheduler.get_current`
after validating the userspace range. `posix_write_for_task_observation_v1`
requires that caller's active descriptor context, resolves the descriptor's
original output sink, and reserves its generation/nonce-bound per-write capture
lease before invoking the inline serial backend. A context mismatch or failed
owner reservation returns EAGAIN before any output. The ordinary path is used
only for a redirected/unobserved sink or a task positively found unobserved
under the owner mutex; serialization failure cannot masquerade as absence.

Output identity belongs to an open file description in `fd_table`, seeded
only for the original stdout/stderr serial sinks. Duplication and fork share
that identity. Thus `dup2(2,1)` emits stderr, while writing to a duplicate of
the original stdout remains stdout. Redirecting to a file or pipe, reopening
descriptor 1/2, and opening another serial descriptor confer no output role.
Final close and object reuse clear the role.

The SOSIX serial owner reads each user byte once into a local value, passes
that value to the HAL, then appends the same value to an observation batch.
No before/after copy of mutable user memory is presented as emitted output.
Batches contain at most 256 bytes; stream retention remains 65536 bytes per
stdout/stderr under the scheduler observation mutex. The callback closes over
the bound lease and stream; SOSIX knows no scheduler types or ambient child.
The backend commits each batch after its bytes have been emitted and before
completing its inline request. It never allocates an observation-sized copy
of an unbounded write.

Invalid descriptors, zero-length writes and request-slot exhaustion emit no
bytes and invoke no observer. The current serial HAL returns no partial-write
status: this backend's accepted prefix is either empty or the emitted loop
prefix. Canonical batch APIs also reject counts outside their supplied bytes
and support explicit accepted prefixes. Their unit specs exercise that owner
contract, not a claimed hardware short-write run.

Capture rejection cannot undo physical output and therefore does not replace
the syscall's real byte count. Each issued lease tracks committed emitted-byte
reports. Finalization reconciles that count against the actual backend return;
a lost callback poisons its stream. Failure to acquire the finalization lock
leaves the lease pending. Each stream admits only one pending write, so at most
two writes (one stdout and one stderr) may be pending per observation. A
same-stream overlap rejects the new write with EAGAIN before emission, preserving
the stream's HAL byte order across task switches between emission and commit.
A pending or failed stream rejects further writes until owner cleanup; the
other stream is independent. Authenticated tickets prevent one successful
write from clearing another's failure or pending state. No retries or
unsynchronized failure markers are used.

The canonical x64 authenticated adoption owner arms capture before publishing
the user task. Generic observations default unarmed, as do unsupported
architectures and commandless compatibility paths. Consumed evidence supplies
`stdout_capture_complete` and `stderr_capture_complete`; each is false for an
unarmed lifecycle, a failed or pending lease, or retention truncation. Both must
be true before the tool probe compares output, including an empty expected
stderr or a completely silent tool. Empty arrays and zero outstanding leases
alone prove no routing. Stale/exited leases reject further commits. Real
HAL/request failure behavior still requires execution qualification; no runtime
admission follows from a callback or a source-level specification alone.

Descriptor operations retain the existing task-owned descriptor-context
serialization contract. This change adds no independent descriptor mutation
domain or cross-task fd table. Observation state has its own canonical mutex;
HAL output completes before that mutex is acquired, so capture does not hold
the observation lock across device I/O.

Regression specs cover sink identity through dup/dup2, file redirection,
serial reopen, final close/reuse, fork inheritance, accepted batch prefixes,
stdout/stderr separation, invalid counts, stale generations, post-exit writes,
missing handles and retention truncation. Completeness specs additionally cover
never-armed silent rows, protected empty streams, a lost stderr append,
pending finalization, exclusive same-stream tickets, independent streams,
stale leases and bounded capacity.
