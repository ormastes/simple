<!-- codex-design -->
# Windows ConPTY for SMUX Detail Design

The Simple API exposes an opaque integer handle. `open` validates positive
dimensions, `spawn` accepts an explicit program, `platform_default_shell`
selects `COMSPEC`/`cmd.exe` on Windows and `SHELL`/`/bin/sh` on Unix, and
`read`, `write`, and `close` delegate to the raw provider.

SMUX opens once, spawns the platform default shell, routes send/capture through
the Simple API, and closes the handle during shutdown. Failed creation or spawn
keeps the existing scrollback behavior without claiming a PTY exists.

## Windows service corrections, 2026-10-16

The production service uses `os.apps.smux.layout.smux_plan_split` for pane
geometry. `vertical`/`v` divides columns; `horizontal`/`h` divides rows. One
cell is reserved for the separator. Both regions must have at least one cell.
Validation and capacity checks precede the single service-state commit; a
rejected split consumes neither a pane slot nor an id. Child spawn remains
explicit, as required by the service API.

Resize refuses nonpositive dimensions before updating geometry or metrics.
This describes service geometry only: notifying a running ConPTY child still
requires a PTY resize provider and runtime evidence.

Client attachment refuses unknown sessions, empty client ids, nonpositive
dimensions, and new clients beyond the four-client table. Refusal uses the
existing `MuxClientAttachment.attached = false` result. Reattaching an existing
client updates its session and dimensions without requiring a free slot;
unrelated client records survive the replacement.

The direct-service SSpec is
`test/03_system/tools/smux_service_features_spec.spl`. It exercises the
production API rather than a local session registry. In-process detach
evidence cannot establish survival after the client process exits. The hosted
line protocol currently owns and shuts down its service; cross-process
detach/reconnect remains an outstanding architecture gap.

## Pure-Simple native Windows provider, 2026-10-16

The native provider is `std.nogc_sync_mut.io.windows_pty_owner`, with direct
kernel32 declarations in `windows_pty_abi` and separately testable UTF8/COORD
logic in `windows_pty_codec`. The Rust/interpreter `std.sys.pty` owner remains
unchanged. Native product builds select the Windows facade through an explicit
ordered source overlay; OS detection alone cannot choose a runtime provider.
This is authored implementation, pending compilation and native qualification.

Each open returns a nonreused logical slot, bounded to 100000 successful opens
and 1024 simultaneously active or quarantined owners. The single-threaded
owner retains a zeroed 16KiB process-heap allocation, native handles, and at
most three incomplete output UTF8 octets. No raw pointer crosses the facade.
Rows and columns must be positive, at most 1000 each, with area at most 262144.
The packed Win64 COORD places columns in the low SHORT and rows in the high
SHORT. Win64 `OVERLAPPED` is 32 bytes, STARTUPINFOEXW 112,
PROCESS_INFORMATION 24, JobObject extended limits 144, and basic accounting 48.
Each address used for an eight-byte field is eight-byte aligned.

ConPTY receives synchronous input/output endpoints as required by Windows.
The input endpoint is a private local named-pipe server; only the owner's
write client uses FILE_FLAG_OVERLAPPED. The first-instance flag rejects an
existing server; remote clients are rejected. All handles are noninherited.
One 4096-byte write buffer, 32-byte OVERLAPPED, and manual-reset event belong
to the owner until completion is observed. `write_some(handle, bytes)` returns
the number of prefix bytes copied into this retained storage, zero for
backpressure, or -1 for error. Positive acceptance is distinct from delivery.
`input_pending(handle) -> Result<bool,text>` polls GetOverlappedResult without
waiting, and reports deferred delivery failures. The compatibility text write
has a 1MiB admission bound and a two-second full-delivery attempt; false may
follow partial delivery and must not cause blind retry of the whole command.

Output reads first use PeekNamedPipe, then consume at most 8192 available
bytes through the exclusively owned reader. An incomplete UTF8 suffix remains
in the slot across polls. Complete output validates before one byte-to-text
conversion; malformed input produces replacement text. Read timeouts are
bounded to 60000ms; the responsive multiplexer uses zero-timeout reads.

Child creation uses a mutable full-UTF16 command line, a pseudoconsole process
attribute (0x20016), STARTUPINFOEXW, CREATE_SUSPENDED, and
EXTENDED_STARTUPINFO_PRESENT with inheritHandles false. A kill-on-close
JobObject admits the suspended process before ResumeThread. The original
ConPTY-side pipe handles are closed after successful process creation.
Resize uses the real ResizePseudoConsole API, rather than changing only the
service geometry.

Close invalidates every alias before teardown. It closes the output read end
before ClosePseudoConsole, preventing a synchronous final-frame write from
deadlocking older Windows; this intentionally discards the final frame at
explicit shutdown. It terminates the owned job, requests cancellation of any
write, and polls completion without waiting. Request buffers cannot be freed
merely because CancelIoEx returned. The slot remains quarantined until its
request is terminal, the retained leader is signaled, and JobObject active
processes are zero. Only then are handles and heap storage released. Subsequent
provider calls reap the bounded quarantine list. `cleanup_pending()` sweeps
without waiting and reports the retained count; -1 permanently records a
native resource-release failure. A false close return means cleanup is deferred
or failed; callers must retain teardown tracking. A repeated close polls that
same logical token and returns true after successful terminal collection. Nothing
claims cross-thread safety or concurrent writes to one slot.

Failed CloseHandle/HeapFree calls preserve the original owned handle/address
for retry. This includes the primary thread, original ConPTY pipe ends,
command-line allocation and attribute-list allocation. An unsuccessful open
whose cleanup fails becomes a private quarantined slot, even though no public
handle was returned. Any release failure permanently rejects a clean-drain
receipt; a later retry cannot erase that evidence. HPCON close is skipped while
the output-reader close is failing, and the arena survives until all retained
handles and auxiliary allocations have been released.

Qualification artifacts (currently unexecuted):

- `test/01_unit/lib/io/windows_pty_codec_spec.spl`: eight value-based scenarios.
- `test/fixtures/compiler_entrypoint/windows_pty_owner/main.spl`: real two-shell
  output, variable-expansion tokens, independent environments, UTF8, live
  resize observed from the child Console dimensions, nonreading-child
  backpressure, terminal job/leader close receipts, and nonreused handles.

The fixture must compile and execute independently with the admitted Phase2
and Phase3 producers. Source inspection and an authored expected stdout file
do not constitute a provider PASS. The broader smux Windows ConPTY SSpecs
remain a separate product integration gate.

Windows API references:

- [CreatePseudoConsole](https://learn.microsoft.com/en-us/windows/console/createpseudoconsole)
- [Creating a pseudoconsole session](https://learn.microsoft.com/en-us/windows/console/creating-a-pseudoconsole-session)
- [ClosePseudoConsole](https://learn.microsoft.com/en-us/windows/console/closepseudoconsole)
- [Synchronous and overlapped pipe IO](https://learn.microsoft.com/en-us/windows/win32/ipc/synchronous-and-overlapped-input-and-output)
- [CancelIoEx](https://learn.microsoft.com/en-us/windows/win32/api/ioapiset/nf-ioapiset-cancelioex)

## Synchronous SOSIX routing, 2026-10-18

REQ-006 adds exact aliases under `std.nogc_sync_mut.sosix` for the existing
host owners: `process`, `time`, `host`, `stdio`, `pty` and `terminal_console`.
These are synchronous compatibility operations and may block exactly as their
owners do. They introduce no ring, scheduler, descriptor registry or async
completion guarantee. `src/os` never imports the async SOSIX capsule.

The PTY/console aliases target the stable `std.sys` capabilities. The ordered
Windows provider overlay still selects the actual ConPTY/console owner. TCP
retains its existing `io.tcp -> sosix.network -> Windows TCP owner` route.
Native Win32 ABI declarations and resource management stay in provider owners.
Clipboard actions remain explicit client actions through the existing console
capability; this repair performs no clipboard access during development.

The stdin alias preserves `text` plus empty-text EOF via the annotated
`sffi.host.read_stdin_line` owner. Output uses an inline-requested SOSIX wrapper
around the original language `print` intrinsic, preserving its text conversion
and newline lowering. It does not assume that a raw `rt_println` foreign call
has the same text marshaling. Startup aliases retain the normalized CLI helper and existing
file/PID contracts. The platform-name alias returns the existing OS name;
fixtures only compare it with `windows`, equivalent to their prior host-family
predicate for this qualification gate.

Clock units remain Unix microseconds and monotonic milliseconds. The sleep
alias targets `concurrent.thread.thread_sleep`; this fixes fixtures that
previously imported a shell-based helper and incorrectly formatted subsecond
delays. No polling algorithm or deadline is changed.

Alias overhead, native symbol ownership and stdout bytes require runtime/link
evidence. Source checks establish routing only. The source spec/manual and
`smux_sosix_host` native control are listed in the test plan; all native results
remain pending an admitted producer. No generic registry, runtime platform
dispatch, new environment read, extra filesystem scan or hot-path shell spawn
is introduced by these aliases.
