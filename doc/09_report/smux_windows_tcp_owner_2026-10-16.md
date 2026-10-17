# Windows native TCP owner qualification

Status: TEST_BLOCKED. Source and executable fixture authored; no execution PASS.

The linked native runtime at `src/runtime/runtime_native.c:16485` supplies failure
stubs for Windows TCP. Windows Rust interpretation uses a different provider;
an OS-only conditional would incorrectly redirect that working path.
`cfg_platform.spl` recognizes OS/family/architecture/CPU keys, with feature keys
currently false; there is no demonstrated native/interpreter selector.

`std.nogc_sync_mut.io.windows_tcp` implements the stable `sffi.net.io_tcp_*`
signatures in Simple over documented Win64 Winsock2 APIs in `windows_tcp_abi`.
Native product source-root composition selects the SOSIX network overlay;
default interpreter source roots retain their existing runtime wrapper owner.
Overlay selection and actual smux execution need their own observed evidence.

The provider is a single event-loop owner. Handles encode generation and slot,
never OS socket values, and must only be passed back to this provider. At most
4096 slots exist; each closed slot is reused with an incremented generation.
`fd = generation * 4096 + slot`, with generation beginning at 1. Every lookup
validates the generation and live state; stale handles cannot act on reused
slots. Generation 2251799813685247 is the last representable value; its slot
retires on closure rather than wrapping. Churn does not consume a lifetime
connection budget. Capacity is checked before OS acquisition. Each live socket owns one
WSAStartup reference; successful close invalidates the slot before WSACleanup.
Accepted sockets obtain their own reference. Admission failure closes acquired
sockets. Heap scratch pointers remain lexical, copied byte data crosses the
public boundary, and all temporary allocations are released before return.
New sockets have HANDLE_FLAG_INHERIT cleared before public admission. Fallible
configuration occurs after internal ownership publication; a failed close
retains its socket/reference in the owner rather than calling WSACleanup.

Numeric IPv4 and `localhost` are supported. Runtime family 0 selects IPv4;
family 1/IPv6, DNS names, and enabling POSIX reuseport explicitly fail.
Bind returns a listening socket, while bind_fd requires separate listen.
Accept/connect defaults and ordinary I/O timeouts are 30 seconds; explicit
timeouts must be positive and fit signed 32 bits. Individual byte transfers
are limited to 1MiB, lines to 64KiB. Writes return actual partial counts;
read returns empty bytes on EOF and nil on failure/would-block/timeout.
Nonblocking partial lines remain buffered in the socket slot for subsequent
line or byte reads. Flush validates SO_TYPE without altering TCP_NODELAY.

The native fixture `test/fixtures/compiler_entrypoint/windows_tcp_owner/main.spl`
binds an ephemeral loopback port, verifies accept timeout, connects a second
socket, accepts, checks endpoint reporting, exchanges octets including zero,
128 and 255, resumes a partial UTF8 line, half-closes for real EOF, and proves
stale logical handles cannot close a later socket. It also checks unsupported
addresses/families, invalid handles, unsupported reuseport and option calls.
It observes three simultaneous live slots, then performs 128 real socket
create/close cycles while verifying that actual registry allocation remains
unchanged, live count returns to zero, and stale reads/closes/options/address
queries fail without affecting the reused live lease.
The fixture closes sockets on both ordinary success and reported failure.

Required remaining gates: qualified Phase2 native compile/run, qualified Phase3
native compile/run, actual smux owner/client cross-process native run through
the selected overlay, Windows interpreter non-regression, required compiler/lib
checks and current SPipe scenario execution. These remain unverified.

ABI source review used the current host SDK `10.0.26100.0/um/WinSock2.h`:
WSADATA Win64 fields at lines 364–378 (408-byte padded layout), socket options
at 434–437, FIONBIO at 220, and poll flags/fields at 1602–1619. This verifies
declared constants/layouts against installed headers, not compiler execution.
Microsoft documents matching each successful startup with cleanup in
[WSAStartup](https://learn.microsoft.com/en-us/windows/win32/api/winsock/nf-winsock-wsastartup)
and finite poll/readiness behavior in
[WSAPoll](https://learn.microsoft.com/en-us/windows/win32/api/winsock2/nf-winsock2-wsapoll).
