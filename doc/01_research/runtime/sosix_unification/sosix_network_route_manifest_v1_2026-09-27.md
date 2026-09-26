# SOSIX network route manifest v1

Status: **partial RU-001 census**, inspected at `acd63771621` on 2026-09-27. This covers the TCP/socket routes named below. It does not qualify a common network provider or close the global RU-001 gate.

## Route keys

| Key | Current route and profile |
|---|---|
| H | Hosted Simple TCP caller → `rt_io_tcp_*` extern → native C runtime or seed interpreter. |
| X | x86_64 SimpleOS syscall 70–77 → C trap switch → strong Simple shim → `socket_compat`/netstack IPC. |
| A | ARM64 SimpleOS user syscall → capability precheck → direct native network path when ready, otherwise Simple shim. |
| P | Portable checked socket core; source currently shows definitions and exports, with no production caller found in `src/os/**`. |
| B | SimpleOS baremetal `rt_net_*` compatibility ABI → pure-Simple socket facade → boot TCP transport. |

## Classified declarations and owners

| Symbol and source | Category and signature | Verified caller → owner → route/profile | Migration disposition |
|---|---|---|---|
| `SOSIX_ID_NET_SEND`, `NET_RECV`, `NET_SEND_TO`, `NET_RECV_FROM`, [`service_ids_v1.spl`](../../../../src/lib/common/contracts/sosix/service_ids_v1.spl) | Common operation IDs `0x0201`–`0x0204`; `u32` constants | Common ID table → contract owner; intended all profiles | Retain IDs. The inspected hosted `std.nogc_async_mut.sosix` modules have no network operation producer or provider; ID reservation alone is not an execution route. |
| `rt_io_tcp_connect`, [`sffi/net.spl`](../../../../src/lib/nogc_sync_mut/sffi/net.spl) | Raw extern `(text) -> i64`, with `io_tcp_connect` inline wrapper | `std.nogc_sync_mut.io.tcp` and Redis client still declare/call raw externs → SFFI/runtime; H | Classify remaining direct callers; preserve connection/error behavior before replacing the raw path with one SOSIX owner. The SFFI wrapper does not itself make callers use it. |
| `rt_io_tcp_connect`, [`runtime_native.c`](../../../../src/runtime/runtime_native.c) and [`interpreter_extern/mod.rs`](../../../../src/compiler_rust/compiler/src/interpreter_extern/mod.rs) | Native C socket/connect implementation; hand-registered seed interpreter extern | Hosted TCP caller → native C or Rust seed implementation; H | Compare native and interpreter errors, timeout, and descriptor lifetime. No generated SOSIX dispatch owns both routes yet. |
| `socket`, `connect`, `bind`, `listen`, `accept`, `socket_send`, `socket_recv`, [`userlib/net.spl`](../../../../src/os/userlib/net.spl) | User socket API; `socket(u32,u32) -> Result<Socket,text>`, connect/bind use `SockAddr`, byte send/recv use `[u8]` | User service → raw syscall 70/72/74 or `rt_simpleos_socket_*_bytes`; SimpleOS target route depends on architecture | Keep the user API while moving effects behind one checked kernel operation owner. The methods currently take different syscall and byte-helper paths. |
| `rt_syscall_dispatch` cases 70–77, [`baremetal_stubs.c`](../../../../examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c) | Live x86_64 C trap, six `u64` arguments → `i64` | Ring-3 syscall → `spl_handle_net_*`; X | **Open authority gap:** these cases call shims directly; this switch does not call `spl_shim_net_capability_check`. The strong shims inspected here also dispatch without the portable exact capability check. Close and test before release. |
| `spl_handle_net_bind` and peers, [`syscall_shim_net.spl`](../../../../src/os/kernel/abi/syscall_shim_net.spl) | Strong C ABI handlers for 70–77; six `u64` → `i64` | x86_64 C switch and ARM64 fallback → `socket_compat`; X/A | Use the existing portable checked owner for bind and other socket effects. Current bind copies the user address and calls `posix_bind` without the exact `NetBindIpv4`/`NetListen` authorization present in the portable core. |
| `portable_net_bind_args_checked_v1`, `portable_net_capability_allowed_v1`, `portable_net_dispatch_v1`, [`syscall_net_portable_v1.spl`](../../../../src/os/kernel/ipc/syscall_net_portable_v1.spl) | Checked socket owner; `(SyscallArgs, Scheduler, IpcManager) -> SyscallResult` or `bool` | P: definitions/exports only in inspected `src/os/**`; tests describe intended RISC-V and x86_64 parity, but no production caller was found. | Connect it to live traps using its single copied sockaddr snapshot and exact bind/listen capability checks. Confirm guest dispatch and denial cases on each architecture. |
| `arm64_dispatch_net_shim`, [`baremetal_stubs.c`](../../../../examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c) | ARM64 user syscall routing for 70–76 | Capability precheck → direct implementation when virtio net is ready, otherwise shim; A | Precheck exists, but its Simple gate currently uses broad `NetConnect(0)`/`NetListen(0)` requests. Reconcile with the portable endpoint-specific owner before claiming cross-architecture parity. |
| `posix_socket`, `posix_bind`, `posix_connect`, `posix_send_bytes`, `posix_recv_bytes`, [`socket_compat.spl`](../../../../src/os/kernel/socket_compat.spl) | Kernel socket/descriptor adapter; typed sockaddr and byte arrays | Simple shims → fd table → netstack IPC port 2 (with loopback handling); X/A. Portable core is an unconnected candidate. | Keep one descriptor/backend owner and error map when migrating to SOSIX. `posix_recv_bytes` currently collapses negative service status into text, so the shim maps it to `-5`. |
| `_handle_net_socket` and `_forward_net_ipc`, [`syscall_net.spl`](../../../../src/os/kernel/ipc/syscall_net.spl) | Legacy generic syscall handler; `SyscallArgs -> SyscallResult` | Generic `syscall_handler` → `_forward_net_ipc` → unconditional `-38`; compatibility route | Do not count this as working network I/O. Retire or redirect only after its callers and syscall filter semantics are resolved. |
| `rt_net_socket`, `rt_net_bind`, `rt_net_send_bytes`, `rt_net_recv_bytes`, [`rt_net_socket_facade.spl`](../../../../src/os/kernel/net/rt_net_socket_facade.spl) | Baremetal C exports over a private socket table and boot TCP transport | `os.kernel.boot.http_baremetal`, DBD, and other `rt_net_*` callers; B | Inventory each caller and authority source. This is a separate compatibility path, not the hosted TCP implementation or SOSIX network provider. |

## Evidence needed for promotion

1. Prove the x86_64 and ARM64 live traps enforce the same exact socket-create, bind, listen, connect, send, and receive authority as the portable owner, including wrong endpoint, absent grant, and changed user-address negatives.
2. Qualify one network operation end to end through the common SOSIX ID, a bounded completion and retirement owner, a hosted provider, and a SimpleOS provider. Test partial I/O, error mapping, cancellation, and socket close while work is pending.
3. Inventory remaining UDP, DNS, TLS, HTTP, and direct `rt_net_*`/`rt_io_tcp_*` callers before declaring RU-001 complete. This manifest does not classify those families.

## Later source candidate

PR #1691 commit `2d453ab592b` routes the x86_64 strong shims for 70–76 through `portable_net_capability_allowed_v1` or the atomic checked-bind helper, and gates 77 with `NetRaw`. This addresses the x86_64 source bypass recorded at the inspected baseline. It has no admitted Simple or ring-3 guest execution evidence. ARM64's separate direct precheck and the absent RV64 production socket route remain open.
