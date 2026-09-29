# Unsupported network aliases and the hardware TCP bool ABI

## Cause

`src/lib/nogc_sync_mut/sffi/net.spl` generated private wrappers for ten
unimplemented `rt_net_*` names: accept, bind, close, init, recv_bytes,
rx_ready, send_bytes, socket, stats, and tx_test. Root and Linux native link
review found no implementations or callers. These dead declarations enter
full CLI native closure scans and produce unresolved native symbols.

The same module also generated a private
`rt_tcp_connect(host: text, port: i64) -> bool` alias. The hardware adapter
called that unsupported bool ABI for health and readiness polling. It
conflicts with the platform-scoped OS realtime declaration
`rt_tcp_connect(host: text, port: i32) -> i32` in
`src/os/realtime/jtag/openocd_probe.spl`, which is preserved unchanged.
This repair makes no claim of an implemented native provider for that raw
platform declaration.

## Repair

Remove exactly those eleven unused private extern/wrapper pairs, retaining
all supported `rt_io_tcp_*` aliases and the unrelated Unix socket alias.
Reclassify exactly eleven entries in `scripts/check/rt_alias_map.sdn` as
`missing`, removing generated module/function/signature metadata and recording
the reason. The migration tool only rewrites entries whose class is `same`
(`src/app/tools/rt_migrate/rewrite.spl:232`), so the removed wrappers are no
longer advertised as mechanically reproducible aliases.

The hardware adapter's three bool probes now call the production leaf
`hardware_tcp_probe(host: text, port: i64) -> bool`. It rejects empty hosts
and ports outside 1–65535, brackets bare IPv6 hosts without doubling existing
brackets, and rejects unmatched brackets. It uses the existing public
`TcpStream.connect_fd_timeout(addr: text, ms: i64) -> i64` with 500ms. Numeric
connection failures return false; a successful handle is closed once through
`tcp_fd_close(fd: i64) -> bool` before returning true. These existing public
`std.nogc_sync_mut.io.tcp` APIs are available on main and release/1.0 without
depending on the main-only generated SFFI alias module. Adapter APIs, retry
counts, sleep intervals and process lifecycle remain unchanged.

The numeric-only provider rejects hostnames with
`-NetError::InvalidAddress` (`-101`). That exact result invokes the existing
`browser_dns_lookup` DNS owner, whose runtime lookup is bounded to 5 seconds.
The probe starts one 5.5-second monotonic deadline before the initial attempt
and tries comma-separated resolved numeric candidates with at most 500ms
each and the remaining shared budget. Empty resolution or deadline expiry
returns false. This preserves `localhost` and other hostname support without
using a heuristic IP parser or adding a runtime ABI. A numeric address's
refused/timed-out result does not enter DNS.

## Verification

`test/01_unit/app/test_daemon/hardware_tcp_probe_spec.spl` imports the
production leaf and uses real ephemeral loopback listeners. It covers open
and refused ports, peer EOF after each probe, sixteen repeated connections,
bare/bracketed IPv6, hostname resolution/fallback, bounded `.invalid` DNS
failure, and invalid input. The raw provider's numeric-only `-101` result for
`localhost` is asserted before testing DNS fallback. EOF is distinguished
from a read failure; accepted peer handles and listeners are explicitly closed.
The tests use the same shared public I/O facade; `TcpStream.read(1)` retains
`Ok(empty bytes)` versus `Err(IoError)` to distinguish EOF from a failed read.
The scenarios establish socket closure only, not allocation-leak freedom.

## Separate pre-existing provider allocation issue

`native_tcp_connect_timeout` allocates a local-address string pointer in
`src/compiler_rust/runtime/src/value/net_tcp.rs:180–204`.
The `rt_io_tcp_connect_timeout` wrapper at `455–464` discards that pointer.
The address allocator in `value/net.rs:226–249` requires explicit pointer/length
release. This source observation needs a separate provider ownership repair;
the Simple probe cannot release a pointer the public wrapper does not return.
Peer EOF does not verify release of this metadata allocation.

Dynamic verification is pending an admitted self-hosted native harness with
the supported network runtime provider. No Rust-only reimplementation or
placeholder pass is accepted as evidence. The earlier admitted TRACE32 mini
compile reached its 180-second startup guard without a verdict; that result
is not repeated or claimed as evidence for this repair.


## 2026-09-29 integration diagnostics

Conflict resolution retains the shared TcpStream/TcpListener facade introduced
in PR #2046. Its scalar connection and close methods delegate to the same
network owner used by the previously landed calls. The integration spec was
invoked through `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`.
The executable identified itself as a Rust-built bootstrap seed, so the result
is diagnostic only and is not admitted self-hosted app verification. Further
app testing through that executable was stopped.

The diagnostic executed seven examples: five passed, while localhost and
`.invalid` hostname cases failed with `semantic: invalid socket address`
before the expected native `-101` fallback. This demonstrates an interpreter
versus native-provider error-contract mismatch; it does not prove a native
probe failure or a successful native test. Log: `/tmp/pr2046-hardware-test.log`.
A supported self-hosted/native provider harness remains required for this gate.
