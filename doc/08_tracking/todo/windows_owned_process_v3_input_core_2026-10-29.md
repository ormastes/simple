# Windows immutable stdin core

Date: 2026-10-29. Status: internal V3 C implementation and native scenarios
prepared; Windows compilation/execution and SSpec execution remain unverified.

The V2 Windows owner now accepts immutable stdin through
`rt_process_owned_start_v3` and reports it through
`rt_process_owned_input_receipt_v3`. Admission copies at most 16 MiB and hashes
that copy before creating the suspended child. The random lease capability
continues to authorize V2 poll/cancel/result/collect. A V2-only token cannot
produce a V3 input receipt; stale or collected authority remains stale.
The Windows owner treats a wrong-family receipt request as EINVAL; the Linux
provider uses EPROTO for that invalid-family request.

The private overlapped named-pipe writer owns a stable OVERLAPPED structure,
event and byte buffer. Each advancement issues at most one 16 KiB write and
records only completed bytes. The pipe name uses independent entropy so the
child cannot recover its owner's lease token from a queried pipe name. Only
the child read handle appears in the inherited std-handle whitelist; remote
clients are refused and first-instance creation prevents pipe-name takeover.
The successful private CreateFileW establishes the connection. Admission does
not issue a redundant ConnectNamedPipe, so there is no pending connection I/O
to abandon on a failed start. The portable fake intentionally provides no
ConnectNamedPipe function, guarding this ownership boundary.

Cancellation/reap requests CancelIoEx, then polls completion without waiting
under the registry lock. Pending cancellation keeps the buffer, event and
pipe alive. Terminal requires the input writer closed after completion in
addition to the existing exact leader wait, empty job membership and closed
output streams. A zero-length snapshot closes its writer immediately and
retains the SHA-256 of empty input. Broken input before cancellation remains
an error; cancellation completion and broken-pipe races close safely.

The opaque Simple V3 facade, independent capture configuration, sealed image
and cwd pins, and V4 still return unsupported. No public capability bits were
enabled. This is a core prerequisite, not full Windows SOSIX qualification.

## Test contracts and evidence

- REQ-WIN-INPUT-001: native binary echo larger than the pipe buffer, caller
  mutation after admission, immutable digest, exact accepted/written lengths,
  empty EOF, stale/wrong-family receipts and invalid admission.
- REQ-WIN-INPUT-002: maximum input to a non-reader, bounded zero-wait poll,
  independent child progress, cancellation completion and partial receipt.
- Portable Win32 API fakes execute the production transport header and verify
  immutable bytes/digest, synchronous and asynchronous partial writes,
  ERROR_IO_INCOMPLETE retention, cancellation racing completion, aborted and
  broken-pipe completion, invalid completion length and zero-input EOF.
- Portable transport compiled with `clang -std=c11 -Wall -Wextra -Werror
  -fsanitize=undefined`: PASS. These are API fakes, not Windows evidence.
- Negative control: the same portable oracle rejected a deliberately modified
  transport that closed/freed input on ERROR_IO_INCOMPLETE. PASS; this checks
  oracle sensitivity, not native Windows red/green execution.
- Existing native macOS non-Unix fallback selfcheck: PASS (existing Darwin
  deprecation/unused-helper warnings; linked with `-Wl,-dead_strip`).
- Windows-native selfcheck built on macOS: SKIP, exit 77. This checks only
  explicit platform refusal.
- Windows-native compilation, six native suites and native Modern SSpec:
  NOT RUN. No Windows SDK or Windows producer is installed on this host.
  Native red/green TDD execution is therefore pending; scenarios were authored
  before implementation without manufacturing a native result.
- ASan attempt: BLOCKED before main in the host sanitizer initialization;
  `sample` showed recursive allocator initialization inside
  `__asan::InitializeShadowMemory` / `StaticSpinMutex::LockSlow`. The process
  was terminated; UBSan execution completed. No ASan PASS is claimed.

Run `sh scripts/check/check-owned-process-windows-input-transport.shs` for the
portable transport checks. On Windows, run
`scripts/check/check-owned-process-windows-async.ps1`, then execute
`test/03_system/runtime/process_owned_windows_async_spec.spl` with an admitted
native Simple producer. Both commands use small existing runtime fixtures;
no Phase2 compiler/bootstrap rebuild is required.

The lifetime rules follow Microsoft's
[Canceling Pending I/O Operations](https://learn.microsoft.com/en-us/windows/win32/fileio/canceling-pending-i-o-operations),
[WriteFile](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile)
and [ConnectNamedPipe](https://learn.microsoft.com/en-us/windows/win32/api/namedpipeapi/nf-namedpipeapi-connectnamedpipe)
contracts. In particular CancelIoEx alone does not authorize freeing the
OVERLAPPED structure or input buffer.
