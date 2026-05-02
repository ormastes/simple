# SSH Serial Transport — Draft Requirements

**Date:** 2026-04-11  
**Status:** Draft  
**Source:** Research in `doc/01_research/local/ssh_serial_transport.md` and `doc/01_research/domain/ssh_serial_transport.md`

---

## Problem Statement

The Simple SSH library (`ssh_ffi.spl`) only supports TCP as transport. There is no way to open an SSH session over a serial port (e.g., `/dev/ttyUSB0`) from Simple code without spawning an external process. Embedded Linux targets connected via UART have no supported connection path.

---

## Option A: ProxyCommand / External Process (No New Code)

Use the OS-level `ProxyCommand` mechanism by spawning `socat` as a subprocess.

### Functional Requirements
- FA-1: `SshSession` can be constructed from a subprocess whose stdin/stdout serve as the transport (i.e., a "process pipe" transport).
- FA-2: Caller specifies a command string (e.g., `socat - /dev/ttyUSB0,b115200,raw,echo=0`) and the SSH client connects through it.
- FA-3: The subprocess is terminated when the `SshSession` is closed.

### Non-Functional Requirements
- NFA-1: No new native FFI needed — use existing process-spawning infrastructure.
- NFA-2: Must work on Linux and macOS (socat availability is a user prerequisite).

### Acceptance Criteria
- AC-A1: `ssh_connect_proxy_cmd("socat - /dev/ttyUSB0,b115200,raw,echo=0", "user", ...)` opens an authenticated SSH session over the serial port.
- AC-A2: Session is closed cleanly (no zombie process) when `session.close()` is called.

---

## Option B: Native Serial Host Driver + libssh2 fd Handshake (Full Integration)

Add a hosted-mode serial port driver and wire it into the SSH library via `libssh2_session_handshake()`.

### Functional Requirements
- FB-1: A new `SerialPort` type in `src/lib/nogc_sync_mut/io/serial_ffi.spl` wraps `/dev/ttyS*` / `/dev/ttyUSB*` on Linux and `/dev/cu.*` on macOS.
- FB-2: `SerialPort` implements `Read + Write + Close` traits.
- FB-3: `serial_open(device: Text, baud: i32) -> Result<SerialPort, IoError>` opens and configures the port (raw mode, no echo, specified baud).
- FB-4: `ssh_connect_serial(port: SerialPort, timeout_ms: i32) -> Result<SshSession, SshError>` performs the SSH handshake over the serial fd using `libssh2_session_handshake()`.

### Non-Functional Requirements
- NFB-1: `serial_open` must configure termios raw mode (no CRLF translation, no echo).
- NFB-2: Must support at minimum: 9600, 19200, 38400, 57600, 115200 baud.
- NFB-3: Only Linux and macOS (POSIX termios); Windows (COM ports) is out of scope.
- NFB-4: No new Rust crate dependency — use `libc` (already present) for termios FFI.

### Acceptance Criteria
- AC-B1: `serial_open("/dev/ttyUSB0", 115200)` returns `Ok(port)`.
- AC-B2: `ssh_connect_serial(port, 5000)` successfully handshakes with a Dropbear daemon on the target.
- AC-B3: `ssh_exec` over the serial session returns correct output.
- AC-B4: Port is released (fd closed) when `SshSession.close()` is called.

---

## Option C: libssh2 Custom SEND/RECV Callbacks (Maximum Flexibility)

Register custom transport callbacks on the libssh2 session so any byte channel (serial, JTAG RTT, shared memory) can serve as SSH transport.

### Functional Requirements
- FC-1: A `SshTransport` trait with `send(buf) -> i32` and `recv(buf) -> i32` methods.
- FC-2: `ssh_connect_transport<T: SshTransport>(transport: T) -> Result<SshSession, SshError>` registers the transport via `LIBSSH2_CALLBACK_SEND` and `LIBSSH2_CALLBACK_RECV`.
- FC-3: A `SerialTransport` struct implements `SshTransport` using the serial driver from Option B.

### Non-Functional Requirements
- NFC-1: Trait-based design allows future transports (JTAG RTT, pipe, shared memory) without modifying the SSH library.

### Acceptance Criteria
- AC-C1: `SerialTransport` implementing `SshTransport` produces a working SSH session.
- AC-C2: A test with a loopback pipe (`socketpair` or `pipe`) validates the callback plumbing without requiring hardware.

---

## Recommended Path

**Short term:** Option A (ProxyCommand subprocess) — zero new FFI, works today with existing `ssh_ffi.spl` if process-pipe transport is plumbed in.

**Medium term:** Option B (native serial driver) — unblocks embedded workflows, clean integration, uses existing libssh2.

**Long term:** Option C (SshTransport trait) — maximal flexibility, enables JTAG/RTT and other exotic transports.

---

## Out of Scope

- Windows COM port support
- SSH server (listener) over serial (only client side)
- PPP/SLIP network stack (handled at OS level, not in Simple)
- Serial port enumeration / device discovery
