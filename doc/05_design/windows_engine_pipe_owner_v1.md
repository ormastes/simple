# Private Windows Engine pipe owner

The transport is a broker-owned native IO capsule. It opens only the installed
local Docker Engine named pipe. Connection slots are bounded and never reused;
their revisions reject stale copies and closed-owner overwrite. Raw HANDLEs and
state load/store remain private in one file. A connection is not an execution
grant, workload ID, supervisor or process registry.

Read and write use separate retained OVERLAPPED structures, completion events
and 64 KiB buffers. Poll never waits. Cancellation requests never free pending
storage. A completed read retains its unread suffix and each Data result obeys
the current call's maximum, including when that maximum shrinks after submission.
No replacement read overwrites the suffix. Unknown immediate read and completion-query
errors retain storage and never imply EOF; collection
requires positive completion and checked native release. Failed descriptor
LocalFree, event/pipe CloseHandle, and arena/path HeapFree retain the same lease.

Admission reads the actual connected pipe's owner/DACL, requires exact SYSTEM
or Builtin Administrators ownership and a protected nonnull DACL, and rejects
untrusted DELETE/WRITE_DAC/WRITE_OWNER, FILE_CREATE_PIPE_INSTANCE,
GENERIC_WRITE or GENERIC_ALL grants. FILE_APPEND_DATA shares the instance-creation
bit, and FILE_GENERIC_WRITE includes that right. Untrusted clients permitted to
create instances would undermine connected-server trust, so even a stock Docker
endpoint is refused unless its actual protected DACL satisfies this policy.
Unknown ACE types
are refused. The connected server PID is observed before/after validation and
bound to that HANDLE. The client uses identification-only SQOS rather than
allowing server impersonation. These checks follow Microsoft's
[named-pipe security](https://learn.microsoft.com/en-us/windows/win32/ipc/named-pipe-security-and-access-rights)
and [client impersonation controls](https://learn.microsoft.com/en-us/windows/win32/ipc/impersonating-a-named-pipe-client).

The owning broker loop must be the first native IO entry and retain its actual
thread for the connection lifetime. All public entries use the same native
pinned-thread guard as the RAW helper owner. There is no implicit thread handoff.

Ordinary writes and explicitly admitted create/start writes are separate APIs.
The broker validates complete payload identity and authorization before either
call. Admitted writes additionally validate context and sample actual time just
before WriteFile. Context digests use the exact raw64 lowercase hexadecimal
ContainerExecRequestV3/birth digest domain, without a prefix or conversion.
A submitted prefix may already affect the Engine; cancellation
and connection collection are never rollback or no-effect evidence.

Status: source-only **NOT_RUN**. Protected endpoint installation/compatibility,
actual Windows security checks, native fault cases, compiled ABI, runtime and
latency/RSS qualification remain required. The implementation makes no Docker
Engine availability or execution claim on unsupported hosts.
