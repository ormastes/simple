# Windows bounded stdin command owner V1

Source-only status: **NOT_RUN / native acceptance pending**. Existing command
V2 remains unchanged. This additive leaf supplies raw bounded stdin/output and
an exact executable pin for the authenticated SSH facade.

## Public port and trust boundary

`windows_stdin_command_begin_v1(request)` and
`windows_stdin_command_step_v1(owner, cancel)` return an optional opaque owner,
optional final result and error. The caller retains the returned owner on every
pending or failed turn. Native process resources cannot be adopted by PID.

The request contains explicit executable/path, expected lowercase SHA256, argv,
explicit environment, absolute cwd, binary input, running timeout, independent
stdout/stderr limits and Unix admission expiry. Input is at most 2105360 bytes;
each output is bounded to 16 MiB. Capture is raw bytes, preserving frame/NUL
boundaries instead of decoding independently read UTF8 chunks.

The lower owner is not an SSH policy parser. The authenticated caller constructs
fixed validated SSH argv, retains its real `HostIdentityStoreV1`, obtains actual
protected key/known-host file/path admission and verifies exact configured path
equality. Raw paths and POSIX modes never establish Windows ACL admission.
Payload bytes go through stdin, never remote shell argument interpolation.

## Native ownership phases

1. Retain a canonical nonreused slot on the existing Windows owner thread.
2. Resolve each actual retained DOS drive root once with
   `GetFinalPathNameByHandleW(VOLUME_NAME_NT)` and retain its volume/file ID.
   Use the accepted GLOBALROOT native volume spelling for all subsequent
   opens, CreateProcess application name, argv0 and cwd; never fall back to a
   DOS drive mapping. Open every native ancestor including the entire SUBST
   suffix without reparse traversal/delete sharing, and compare the reopened
   selected root against its original volume serial plus 128-bit file ID.
   Then open the final executable without write/delete sharing.
3. Hash the actual retained executable HANDLE incrementally through CNG: at most
   65536 bytes per step, with a 64 MiB file-size bound. Hold the actual file and
   ancestor handles through process termination/reaping and cleanup.
4. Allocate startup/observation buffers, output pipes, CSPRNG-named private
   stdin pipe, protected owner/SYSTEM security descriptor and completion events.
5. Pair the exact local stdin client, observe its real parent process ID and
   retain only that client plus stdout/stderr writers in HANDLE_LIST.
6. Create a kill-on-close JobObject and suspended process, assign it, then resume
   only after actual Unix expiry checks. Running timeout uses monotonic time.
7. Close parent copies of child-only endpoints. Each running step drains at most
   4096 bytes per output and submits or completes one 4096-byte stdin chunk.
   Only actual completion increases `input_written`; queued bytes do not.
8. On failure/cancel, terminate the actual process/job, observe leader signal
   and empty job, cancel/complete retained overlapped IO, then release resources.

Named stdin uses overlapped IO because anonymous pipe writes can block while a
child is also blocked on output. `CreateNamedPipeW` supplies first-instance and
overlapped flags; the retained outbound server writes to the inheritable read
client. No arbitrary endpoint can be injected by the caller. See Microsoft's
[open-mode contract](https://learn.microsoft.com/en-us/windows/win32/ipc/named-pipe-open-modes)
and [CreateNamedPipeW contract](https://learn.microsoft.com/en-us/windows/win32/api/namedpipeapi/nf-namedpipeapi-createnamedpipew).

## Cleanup and returned facts

| Acquired resource | Release rule |
|---|---|
| Process/thread/job handles | Require actual leader/job terminal observation before final release |
| Pending connect/write request | Retain OVERLAPPED, event, pipe and buffer until actual completion or recognized terminal cancellation |
| Pipe/event/file/ancestor handle | Failed CloseHandle retains the same handle for retry |
| CNG hash/provider | Failed destruction/close retains the same CNG owner |
| LocalAlloc security descriptor | Failed LocalFree retains the descriptor |
| Heap allocation | Failed HeapFree retains the allocation |

Cleanup attempts one owned resource release per step. No positive-duration
wait or Sleep is hidden in a callback. An OS syscall's own latency is not yet
qualified. The result reports actual byte completion, stdin closure, output
EOF/truncation, executable digest, leader/job reaping and final cleanup facts.
`effect_attempted` becomes true immediately before CreateProcessW; a later
error cannot retroactively turn that into a no-effect claim.

Only an error-free result with all input written/closed, both output EOFs,
matching executable digest, no truncation and reaped/cleanup-confirmed facts is
eligible for upper frame decoding. These remain local transport facts: remote
effects require the authenticated response and original operation oracle.

## Qualification

Nine production-helper cases are authored, NOT_RUN. Actual Win64 API binding,
incremental pin identity, protected pipe pairing, IO completion, callback
latency, termination, reaping and every failed cleanup path require independent
source review plus separately admitted native evidence. The native acceptance
inventory records missing coverage; no placeholder native success is supplied.

Request arrays are explicitly deep-frozen by production `begin`, and environment
sorting uses another private array. The maximum 2 MiB input copy and bounded
UTF16 path conversion still need latency qualification. Native-volume process
creation compatibility is NOT_RUN; unsupported paths/APIs fail closed without
reopening the original mutable DOS spelling. The actual root resolution API
contract is documented by
[Microsoft](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-getfinalpathnamebyhandlew).
