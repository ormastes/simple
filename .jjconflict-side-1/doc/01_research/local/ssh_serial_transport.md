# SSH Serial Transport — Local Research

**Date:** 2026-04-11  
**Feature:** Custom serial communication layer for SSH  

## User Request

> how add custom serial communication layer to ssh

## Summary

The Simple codebase already has all the necessary primitives: an SSH binding (`ssh_ffi.spl`), transport trait abstractions (`traits.spl`), and both high-level (TCP/TLS) and low-level serial implementations. No serial SSH transport bridge exists yet, but one can be assembled from existing pieces.

---

## Existing SSH Implementation

**File:** `src/lib/nogc_sync_mut/io/ssh_ffi.spl`  
**Backend:** Rust `ssh2` crate (wraps libssh2)

### Key Types
| Type | Purpose |
|---|---|
| `SshSession` | Top-level session handle (auth, channels) |
| `SshChannel` | Exec / shell / tunnel channel |
| `SftpSession` | SFTP subsystem |
| `SshExecResult` | stdout/stderr + exit code from exec |
| `SftpFileInfo` | File metadata for directory listing |

### Key Functions
- `ssh_connect(host, port, timeout)` → `SshSession`
- `ssh_auth_password(session, user, pass)` → `bool`
- `ssh_auth_pubkey(session, user, key_path, passphrase)` → `bool`
- `ssh_auth_agent(session, user)` → `bool`
- `ssh_exec(session, cmd)` → `SshExecResult`
- `ssh_channel_open(session)` → `SshChannel`
- `ssh_port_forward(session, remote_host, remote_port, local_port)` → `bool`
- `sftp_open(session)` → `SftpSession`

### Gap
`ssh2` crate's `Session::handshake()` accepts any `TcpStream`-like Fd. The Simple FFI layer currently hardcodes TCP — there is no hook to supply a custom fd (e.g., a serial port fd). Adding a serial transport requires either:
1. A new FFI entry point `ssh_connect_fd(fd)` using `libssh2_session_handshake()` with an arbitrary fd, or
2. Using the ProxyCommand approach entirely at the OS level (no code change needed in Simple).

---

## Transport Trait Abstraction

**File:** `src/lib/common/io/traits.spl`  
**Traits:** `Read`, `Write`, `Seek`, `Close`

All I/O implementations (TCP, TLS, files) implement these traits. A serial port wrapper would need to implement `Read + Write + Close` to be composable with the existing SSH transport.

---

## Network Transport Implementations

| File | Type | Implements |
|---|---|---|
| `src/lib/nogc_sync_mut/io/tcp.spl` | `TcpStream`, `TcpListener` | `Read`, `Write`, `Close` |
| `src/lib/nogc_sync_mut/io/tls_ffi.spl` | `TlsClientConnection`, `TlsServerConnection` | `Read`, `Write`, `Close` |
| `src/lib/nogc_sync_mut/io/udp.spl` | `UdpSocket` | `Close` |
| `src/lib/nogc_sync_mut/io/http_ffi.spl` | HTTP client/server, WebSocket | — |

---

## Serial / UART Implementations

### Baremetal x86 COM Driver
**File:** `src/lib/nogc_async_mut_noalloc/baremetal/x86/serial.spl`
- COM1–COM4 support with register-level control
- Baud rate, parity, stop bits, FIFO configuration
- Functions: `serial_init(port, baud)`, `serial_write(port, byte)`, `serial_read(port)`, `serial_println(port, text)`
- **No-alloc baremetal** — not directly usable in hosted std environment

### UART Model (RISC-V 64)
**File:** `src/app/hardware/rv64gc/periph/rv64_uart.spl`
- 16550-compatible UART simulation, 16-byte FIFO
- Used for CPU emulation, not direct hardware access

### Baremetal I/O Abstraction
**File:** `src/lib/nogc_async_mut_noalloc/io/baremetal_io.spl`
- `SemihostReader` / `SemihostWriter` — semihosting interface (OpenOCD RTT compatible)
- `UartWriter` — memory-mapped UART writes

### Gap
No hosted-mode (`nogc_sync_mut`) serial port driver exists (e.g., wrapping `/dev/ttyUSB0` via `libc::open` + `termios`). This is the key missing piece for SSH-over-serial on Linux/macOS hosts.

---

## Existing ProxyCommand / Process I/O

The build system and CLI code (under `src/app/`) likely have process spawning with stdin/stdout pipes (used for subprocesses, MCP servers). A ProxyCommand wrapper could reuse this infrastructure — spawn `socat - /dev/ttyUSB0,...` and pipe its stdio as the SSH transport — without any libssh2 change.

---

## Relevant Source Locations

```
src/lib/nogc_sync_mut/io/
  ssh_ffi.spl          # SSH session and channels (libssh2 wrapper)
  tcp.spl              # TcpStream / TcpListener
  tls_ffi.spl          # TLS client/server
  
src/lib/common/io/
  traits.spl           # Read, Write, Seek, Close traits

src/lib/nogc_async_mut_noalloc/
  baremetal/x86/serial.spl   # COM port driver (baremetal only)
  io/baremetal_io.spl        # Semihost / UART writers
```

---

## Conclusions

1. **Easiest path (no code change):** ProxyCommand using `socat` or `ser2net` from the SSH client config. Works with existing `ssh_ffi.spl` if the host-side SSH invocation uses a config file or command-line override.
2. **Library path:** Add `ssh_connect_fd(raw_fd: i32)` FFI function in `ssh_ffi.spl` using `libssh2_session_handshake()` + a new `serial_open_host(dev, baud)` FFI in a new `src/lib/nogc_sync_mut/io/serial_ffi.spl` file.
3. **Reuse existing:** The `Read + Write` trait plumbing is already in place; a serial wrapper just needs to plug into it.
