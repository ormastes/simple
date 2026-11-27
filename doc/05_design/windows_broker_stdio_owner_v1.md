# Windows broker child stdio owner

Status: source-only **NOT_RUN**. This profile is for the pinned private broker
binary. It does not provide general application process or handle access.

Managed `broker-raw` uses the existing PTY slot, file pin, hard Job limits,
suspended admission, deadline checks, exact HANDLE_LIST and descendant cleanup.
The `raw` anonymous-output branch keeps its existing behavior. Broker output
uses a byte-mode FIRST_PIPE_INSTANCE/REJECT_REMOTE_CLIENTS read server owned by
the parent and an overlapped write client inherited by the child. Child stdout
and stderr are the same endpoint; the parent closes its child-only copies before
resume. No ConPTY or additional process supervisor is created.
The broker output client requests GENERIC_WRITE|FILE_READ_ATTRIBUTES
(`0x40000080`), so its GetNamedPipeInfo admission query has the required rights.
Microsoft specifies this combination for a write-only client that reads pipe
settings in [CreateNamedPipe](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-createnamedpipea)
and [named-pipe open modes](https://learn.microsoft.com/en-us/windows/win32/ipc/named-pipe-open-modes).

The child owner captures only GetStdHandle input/output/error. It requires exact
merged output/error, distinct input/output, native PIPE types, byte server input
and byte client output. Actual FileModeInformation must report synchronous input
and asynchronous output before any protocol read or write. Invocation arguments
are not file-mode evidence. The private helper dynamically resolves ntdll's
NtQueryInformationFile, following the existing Windows private-file owner
precedent. Its opaque 64-byte query storage uses SDK IO_STATUS_BLOCK, an ULONG
mode and native size/alignment checks. For a pending query, a zero-time wait must
observe completion on that exact handle before an interlocked IOSB terminal-status
observation. No other operation uses the handle during admission. WAIT_TIMEOUT,
WAIT_FAILED and unknown wait results retain query ownership for a later poll.
Simple code never assumes an IO_STATUS_BLOCK layout or adds an ntdll linker flag.
The documented ABI is [NtQueryInformationFile/FileModeInformation](https://learn.microsoft.com/en-us/windows-hardware/drivers/ddi/ntifs/nf-ntifs-ntqueryinformationfile)
and [FILE_MODE_INFORMATION](https://learn.microsoft.com/en-us/windows-hardware/drivers/ddi/ntifs/ns-ntifs-_file_mode_information).

There is exactly one stdio lease per child process lifetime and no reopening,
including after failed open or collection. Every entry uses the existing pinned
owner-thread guard. The owner stores all endpoint handles, events, the query and
write buffers before returning a cleanup-bearing failure. No raw HANDLE or
mutable state port is public. The lease is not execution authorization.

Input has exactly one reader. PeekNamedPipe counts available bytes; ReadFile
requests at most that count and the current caller bound (up to 64 KiB).
This is nonblocking only under the enforced deployment profile: no CRT reader,
other thread or other component consumes the input pipe. Zero availability and
zero successful read are Pending; only actual broken/disconnected pipe errors
produce End. The child must send all binary protocol output through this owner
and must not print diagnostics through stdout or stderr.

Output has one bounded OVERLAPPED write at a time and a distinct retained 64 KiB
buffer. write_some reports the accepted prefix; pending completion applies
backpressure. An unknown write result fails the owner and forbids replay.
Cancellation requests do not discharge ownership. Pending mode queries retain
their exact handles, SDK storage and arena until the actual IOSB becomes
terminal. Pending writes require actual GetOverlappedResult terminal completion.
Collection then checks each unique handle close and HeapFree, retaining failures
for retry. Stdout/stderr aliases are closed once. There is no cleanup/no-effect
claim about an Engine operation or about the enclosing Job.

Windows fixtures must validate both real file-mode profiles, query pending/error
paths, arbitrary split protocol bytes, full output backpressure, disconnects,
owner-thread refusal, cancellation races and failed releases. Compiled imports,
ABI, runtime, performance and Windows deployment qualification remain NOT_RUN.
