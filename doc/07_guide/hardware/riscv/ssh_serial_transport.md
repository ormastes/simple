# SSH over Serial Transport Guide

Connect to embedded Linux targets (Dropbear, OpenSSH) over a UART serial link — directly from Simple code or via Claude Code's `serial-mcp` MCP tools.

---

## Prerequisites

| Path | Host requirement | Target requirement |
|------|-----------------|-------------------|
| **socat** (default) | `socat` installed | `sshd` running (Dropbear/OpenSSH) |
| **native** | `bin/simple` in PATH | `sshd` running |

Both paths require `ssh` client on the host. The target device must have an SSH daemon listening (on any port — the serial link bypasses TCP).

---

## Quick Start

### socat path (simplest)

```simple
use std.nogc_sync_mut.io.ssh_serial.{ssh_serial_run}

val result = ssh_serial_run("/dev/ttyUSB0", 115200, "root", "uname -a")
print(result.stdout)
```

### native path (no socat dependency)

```simple
use std.nogc_sync_mut.io.ssh_serial.{ssh_serial_run_native}

val result = ssh_serial_run_native("/dev/ttyUSB0", 115200, "root", "cat /proc/cpuinfo")
print(result.stdout)
```

---

## API Reference

### `serial_ffi.spl` — Raw serial port

```simple
use std.nogc_sync_mut.io.serial_ffi.{SerialPort, serial_open, serial_read, serial_write, serial_close, serial_flush, serial_set_timeout}

# Open a serial port in raw mode
val port = serial_open("/dev/ttyUSB0", 115200)
if port.is_valid:
    serial_write(port, "AT\r\n")
    val response = serial_read(port, 256)
    print(response)
    serial_close(port)
```

| Function | Signature | Description |
|----------|-----------|-------------|
| `serial_open` | `(device: text, baud: i64) -> SerialPort` | Open device in raw mode |
| `serial_close` | `(port: SerialPort) -> bool` | Close the fd |
| `serial_read` | `(port: SerialPort, max_bytes: i64) -> text` | Read up to N bytes (5s timeout) |
| `serial_write` | `(port: SerialPort, data: text) -> i64` | Write bytes, return count |
| `serial_flush` | `(port: SerialPort) -> bool` | Drain output buffer |
| `serial_set_timeout` | `(port: SerialPort, timeout_ms: i64) -> bool` | Set read timeout (−1 = block) |

**Supported baud rates:** 50, 75, 110, 134, 150, 200, 300, 600, 1200, 1800, 2400, 4800, 9600, 19200, 38400, 57600, 115200, 230400

### `ssh_serial.spl` — SSH over serial

```simple
use std.nogc_sync_mut.io.ssh_serial.{
    SshSerialSession, SshSerialExecResult,
    ssh_serial_connect, ssh_serial_exec, ssh_serial_run,
    ssh_serial_connect_native, ssh_serial_exec_native, ssh_serial_run_native
}
```

| Function | Transport | Description |
|----------|-----------|-------------|
| `ssh_serial_connect(device, baud, user)` | socat | Build session struct |
| `ssh_serial_exec(session, cmd)` | socat | One-shot exec |
| `ssh_serial_run(device, baud, user, cmd)` | socat | Connect + exec in one call |
| `ssh_serial_connect_native(device, baud, user)` | native | Build session struct |
| `ssh_serial_exec_native(session, cmd)` | native | One-shot exec |
| `ssh_serial_run_native(device, baud, user, cmd)` | native | Connect + exec in one call |

**`SshSerialExecResult` fields:** `exit_code: i64`, `stdout: text`, `stderr: text`

---

## MCP Tools for Claude Code

### Setup

1. The `serial-mcp` server is pre-registered in `.mcp.json`:
   ```json
   "serial-mcp": {
     "command": "bin/serial_mcp_server",
     "args": [],
     "env": { "SIMPLE_LOG": "error", "RUST_LOG": "error" }
   }
   ```

2. Build the server binary:
   ```bash
   bin/simple build
   # Creates bin/serial_mcp_server symlink
   ```

3. Reload MCP in Claude Code:
   ```
   /mcp reload
   ```

### Available Tools

| Tool | Parameters | Description |
|------|-----------|-------------|
| `ssh_serial_connect` | `device`, `baud`, `user`, `path?` | Validate connection params |
| `ssh_serial_exec` | `device`, `baud`, `user`, `cmd`, `path?` | Run command on target |
| `serial_open` | `device`, `baud` | Open raw serial port → handle |
| `serial_write` | `handle`, `data` | Write to open port |
| `serial_read` | `handle`, `max_bytes?` | Read from open port |

`path` is optional: `"socat"` (default) or `"native"`.

### Example Claude Code Prompts

```
Connect to /dev/ttyUSB0 at 115200 baud as root and run `uname -a`
```

```
Open /dev/cu.usbserial at 9600 and send "AT\r\n", then read the response
```

```
Use native transport to check /proc/version on the embedded device at /dev/ttyUSB0
```

---

## Transport Paths Explained

### socat path (default)

Spawns:
```
ssh -o StrictHostKeyChecking=no -o BatchMode=yes \
    -o ProxyCommand="socat - /dev/ttyUSB0,b115200,raw,echo=0" \
    -l root localhost -- uname -a
```

`socat` bridges the serial device to OpenSSH's stdin/stdout pipe, which becomes the SSH transport. No kernel IP stack needed.

**Requirements:** `socat` and `ssh` on host, `sshd` on target.

### native path

Spawns:
```
ssh -o StrictHostKeyChecking=no -o BatchMode=yes \
    -o ProxyCommand="bin/simple serial-proxy /dev/ttyUSB0 115200" \
    -l root localhost -- uname -a
```

`serial_proxy.spl` relays stdin↔serial using the built-in `serial_ffi.spl` driver. No socat.

**Requirements:** `bin/simple` and `ssh` on host, `sshd` on target.

---

## Troubleshooting

| Symptom | Likely cause | Fix |
|---------|-------------|-----|
| `rt_serial_open: open(/dev/ttyUSB0) failed: Permission denied` | User not in `dialout`/`uucp` group | `sudo usermod -aG dialout $USER` (Linux) |
| `ssh: connect to host localhost port 22: Connection refused` | sshd not running on target | `dropbear -F -E -p 22` on target |
| `socat: E open("/dev/ttyUSB0"): No such file or directory` | Wrong device path | Check `ls /dev/tty*` or `ls /dev/cu.*` |
| SSH hangs waiting for input | Target isn't sending SSH banner | Check baud rate matches on both ends |
| `rt_serial_open: unsupported baud rate 250000` | Non-standard baud | Use a standard rate or patch `int_to_baud` in `serial.rs` |
| `is_valid=false` from `serial_open` | Device doesn't exist or permission denied | Check path and permissions |

### Verifying socat is available

```bash
which socat || brew install socat   # macOS
which socat || apt install socat    # Linux
```

### Typical embedded Linux setup

```bash
# On the target (over existing UART console or first-time setup):
opkg install dropbear    # OpenWrt
# or
apt install openssh-server   # Debian/Raspbian

# Start sshd on the serial tty directly:
/usr/sbin/dropbear -F -E -s -p 22
```

---

## Device Paths by Platform

| Platform | USB serial | Built-in serial |
|----------|-----------|-----------------|
| Linux | `/dev/ttyUSB0`, `/dev/ttyACM0` | `/dev/ttyS0` |
| macOS | `/dev/cu.usbserial-*`, `/dev/cu.SLAB_USBtoUART` | `/dev/cu.serial0` |
| FreeBSD | `/dev/cuaU0` | `/dev/cuaa0` |

---

## Architecture Notes

- Both SSH paths are **one-shot per exec** — there is no persistent SSH session object. Each `ssh_serial_exec` call spawns `ssh`, authenticates, runs the command, and exits.
- The `SerialPort` handle from `serial_open` is a raw POSIX fd (integer). It persists until you call `serial_close`.
- The MCP server is stateless: `serial_open` returns the fd as an integer in the JSON response; the client passes it back on subsequent `serial_write`/`serial_read` calls.
- `serial.rs` uses the `nix` crate's `termios` feature (already a runtime dependency) — no new Cargo dependencies.
