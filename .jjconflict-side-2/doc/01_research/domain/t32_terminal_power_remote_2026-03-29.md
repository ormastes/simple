# Research: T32 Terminal, Power Control & Remote Test Runner

**Date:** 2026-03-29
**Scope:** SSH/telnet/SWD serial terminals, hardware power control, relay interfaces, remote test execution
**Status:** Complete

---

## 1. SSH Protocol

### 1.1 Overview

SSH (Secure Shell, RFC 4253) provides encrypted communication over TCP port 22. The protocol has three layers:

1. **Transport layer** -- server authentication, key exchange, encryption (AES-CBC, ChaCha20)
2. **User authentication layer** -- client identity verification
3. **Connection layer** -- multiplexed channels (shell, exec, SFTP, port forwarding)

### 1.2 Authentication Methods

**Password authentication:**
- Client sends username + password in encrypted channel
- Simple to configure but weaker than key-based
- Passwords must be stored encrypted at rest (AES-CBC with master key)
- Vulnerable to brute-force if server allows unlimited attempts

**Public key authentication:**
- Client proves possession of private key matching server's authorized_keys
- Key types: RSA (2048+ bits), Ed25519 (preferred), ECDSA
- Private key can be passphrase-protected (decrypted locally)
- No password transmitted; strongest common method

**SSH agent forwarding:**
- Client delegates key operations to a running ssh-agent process
- Agent holds decrypted keys in memory
- Forwarding allows using local keys on remote hosts (hop through bastion)
- Risk: compromised remote host can use forwarded agent

### 1.3 Exec vs Shell Channels

- **Exec channel:** single command execution, returns exit code + stdout/stderr. Stateless.
- **Shell channel:** interactive PTY, persistent session. Required for telnet-like interaction.
- For test execution, exec channels are preferred (clean exit codes, no prompt parsing).

### 1.4 SFTP

- SSH File Transfer Protocol runs over SSH connection layer
- Used for uploading test binaries to remote hosts
- Operations: open, read, write, stat, mkdir, rename, remove

---

## 2. Telnet Protocol

### 2.1 Overview (RFC 854)

Telnet provides bidirectional text communication over TCP (default port 23). All data is plaintext -- no encryption. Suitable only for isolated lab networks or legacy equipment.

### 2.2 IAC Commands

The Interpret As Command (IAC) byte `0xFF` signals in-band control:

| Sequence | Meaning |
|----------|---------|
| `FF FB xx` | WILL option xx |
| `FF FC xx` | WONT option xx |
| `FF FD xx` | DO option xx |
| `FF FE xx` | DONT option xx |
| `FF F1` | NOP |
| `FF F2` | Data Mark |
| `FF F4` | Interrupt Process |
| `FF FA xx ... FF F0` | Subnegotiation |

### 2.3 Option Negotiation

Common options relevant to terminal automation:

| Option | Code | Behavior |
|--------|------|----------|
| ECHO | 1 | Server echoes input (WILL ECHO = server echoes) |
| SGA | 3 | Suppress Go Ahead (character-at-a-time mode) |
| TTYPE | 24 | Terminal type negotiation |
| NAWS | 31 | Window size |
| LINEMODE | 34 | Line editing mode |

Minimal client strategy:
- Respond WILL SGA (suppress go-ahead for smooth automation)
- Respond WONT ECHO (let server handle echo)
- Reject all other options with DONT/WONT

### 2.4 Login Detection

Telnet has no structured authentication. Login is prompt-based:
- Detect "login:" or "Username:" prompt, send username + CR
- Detect "Password:" prompt, send password + CR
- Detect shell prompt (configurable regex, e.g., `$`, `#`, `>`) to confirm success

---

## 3. T32 SWD Serial Terminal

### 3.1 TERM Window

TRACE32 provides a built-in terminal emulator via the TERM window system. This allows reading/writing serial data from the target's SWD debug port without a physical UART connection.

### 3.2 TERM.GATE SWD

```practice
TERM.GATE SWD
```

Configures the TERM window to use SWD (Serial Wire Debug) as the transport. Data is tunneled through the debug probe's SWD interface, sharing the same physical connection as debug traffic.

### 3.3 TERM.Method

```practice
TERM.Method SWD
```

Alternative configuration command. Selects SWD as the terminal method. Exact behavior depends on T32 version and probe type.

### 3.4 TERM.Out

```practice
TERM.Out "Hello target" 0x0A
```

Sends data to the target through the SWD terminal channel. Accepts string literals and hex byte values. Used to write commands to the target's terminal input buffer.

### 3.5 Reading Terminal Output

Terminal output is captured via the TERM window. Using the T32 Remote Control Library (RCL), the window content can be read programmatically:

- `t32_capture_window_text(client, "TERM.A")` -- captures current text buffer
- Poll-based: minimum interval of 200ms to avoid overloading the probe
- Channel names: `TERM.A`, `TERM.B`, etc. for multiple terminal windows

### 3.6 Integration with Trace32Client

The existing `Trace32Client` in `src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl` provides RCL connectivity. The T32 SWD terminal reuses this connection to issue PRACTICE commands and read window content via `t32_window_capture.spl`.

---

## 4. Power Button Models

### 4.1 PC (ACPI)

Standard PCs use ACPI power management:

- **Power button:** Single toggle. Short press triggers ACPI power event (S0 -> S5 or S5 -> S0). Same physical button for on and off.
- **Reset button:** Triggers hardware reset (warm reboot). Always available when powered.
- **Software shutdown:** `shutdown -h now` (Linux), `shutdown /s` (Windows) for clean OS shutdown.
- **State detection:** Ping, SSH port probe, or IPMI sensor.

Key constraint: Cannot distinguish "press to turn on" from "press to turn off" without knowing current state. Toggle-only devices must track state internally.

### 4.2 Embedded Boards

- **Reset button only.** Power comes from USB or external supply (always on when connected).
- No software power control. Power cycling requires physically disconnecting power or using a relay.
- Reset is the primary recovery mechanism.

### 4.3 Relay / Smart PDU (Discrete On/Off)

- **Discrete control:** Relay open = off, relay closed = on. Separate on/off operations.
- **USB relay boards:** Controlled via serial commands (e.g., HID-based relay modules).
- **GPIO relay:** Raspberry Pi or similar SBC drives relay coil via GPIO pin.
- **Smart PDU:** Network-controlled power distribution unit. SNMP or HTTP API for per-outlet control.
- State is physically observable (relay position = power state).

### 4.4 T32 Probe (Software)

- **`SYStem.Up`** -- Powers up target and enters debug mode. Discrete "on" operation.
- **`SYStem.Down`** -- Powers down target debug interface. Discrete "off" operation.
- **`SYStem.RESetTarget`** -- Hardware reset via debug port (SRST pin). Does not change power state.
- **State query:** `EVAL STATE.RUN()` returns target run state (can infer power).
- No toggle operation -- all commands are discrete.

---

## 5. Wake-on-LAN (WoL)

### 5.1 Magic Packet Format

A WoL magic packet is a UDP broadcast containing:

1. **Synchronization stream:** 6 bytes of `0xFF`
2. **Target MAC address:** repeated 16 times (96 bytes)
3. **Optional password:** 0, 4, or 6 bytes

Total: 102 bytes minimum (6 + 6*16), up to 108 bytes with password.

### 5.2 Transmission

- Send as UDP broadcast to port 9 (or 7)
- Destination: `255.255.255.255` or subnet broadcast (e.g., `192.168.1.255`)
- Target NIC must have WoL enabled in BIOS and OS driver
- Works across VLANs only with directed broadcast or relay agent

### 5.3 Limitations

- One-way: no acknowledgment. Must probe (ping/SSH) to confirm wake.
- Requires known MAC address.
- Some NICs require "magic packet only" mode vs "any packet" mode.

---

## 6. IPMI Power Control

### 6.1 Overview

Intelligent Platform Management Interface (IPMI) provides out-of-band hardware management via a Baseboard Management Controller (BMC).

### 6.2 Power Commands

Using `ipmitool` (or raw IPMI packets):

| Command | Effect |
|---------|--------|
| `chassis power on` | Power on |
| `chassis power off` | Hard power off (immediate) |
| `chassis power cycle` | Off then on (with delay) |
| `chassis power reset` | Hardware reset |
| `chassis power soft` | ACPI soft shutdown |
| `chassis power status` | Query: "on" or "off" |

### 6.3 Relevance

IPMI is available on server-class hardware. For the Simple project, IPMI support is deferred (can be added as a power controller kind later). The `.shs` script interface can wrap `ipmitool` commands as an interim solution.

---

## 7. Relay Controller Interfaces

### 7.1 USB Relay Boards

Common USB relay modules (e.g., FTDI-based, HID-based):

- **HID relay:** Appears as USB HID device. Controlled via `hidapi` or `usbrelay` command-line tool.
- **Serial relay:** Appears as `/dev/ttyUSBx`. Controlled via serial commands (vendor-specific protocol).
- **Example:** `usbrelay` command: `usbrelay BITFT_1=1` (turn on), `usbrelay BITFT_1=0` (turn off).

### 7.2 GPIO Control

On SBCs (Raspberry Pi, BeagleBone):

```bash
# Export GPIO pin
echo 17 > /sys/class/gpio/export
echo out > /sys/class/gpio/gpio17/direction
# Relay on
echo 1 > /sys/class/gpio/gpio17/value
# Relay off
echo 0 > /sys/class/gpio/gpio17/value
```

### 7.3 Script Abstraction

Rather than implementing vendor-specific protocols directly, relay control uses `.shs` shell scripts as an abstraction layer. Each relay board vendor provides (or the user writes) scripts that implement the contract:

- `relay_on.shs` -- turn relay on (exit 0 = success)
- `relay_off.shs` -- turn relay off
- `relay_state.shs` -- print "on" or "off" to stdout
- `relay_reset.shs` -- cycle relay (off, delay, on)

This allows supporting any relay hardware without code changes.

---

## 8. Existing Project Assets

### 8.1 SSH FFI

**Path:** `src/lib/nogc_sync_mut/io/ssh_ffi.spl`

Provides extern functions wrapping libssh2:
- `rt_ssh_connect(host, port, username, password)` -- password auth
- `rt_ssh_connect_key(host, port, username, key_path)` -- pubkey auth
- `rt_ssh_exec(session, command)` -- execute command
- `rt_sftp_init(session)` -- initialize SFTP subsystem
- `rt_sftp_upload(sftp, local_path, remote_path)` -- upload file
- `rt_ssh_disconnect(session)` -- close connection

### 8.2 Trace32Client

**Path:** `src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl`

RCL client for TRACE32:
- Connects to T32 via TCP (default port 20000)
- Executes PRACTICE commands
- Reads register/memory values
- Used by existing 36 T32 MCP tools

### 8.3 T32 Window Capture

**Path:** `src/lib/nogc_sync_mut/debug/remote/protocol/t32_window_capture.spl`

- `t32_capture_window_text(client, window_name)` -- captures text content of a T32 window
- Reusable for reading TERM window output

### 8.4 AES Encryption

**Path:** `src/lib/common/aes/`

- AES-CBC encryption/decryption
- Used for encrypting stored credentials (passwords in SDN config)

### 8.5 BCrypt Key Derivation

**Path:** `src/lib/common/bcrypt/key_derivation.spl`

- Derives encryption keys from master key file
- Combined with AES for credential encryption/decryption

### 8.6 TCP Sockets

**Path:** `src/lib/nogc_sync_mut/net/tcp.spl`

- `TcpStream` -- basic TCP client
- Foundation for telnet client implementation

### 8.7 Session Adapter

**Path:** `src/app/test_daemon/session_adapter.spl`

- Adapter pattern for test daemon sessions
- Reference for implementing remote PC test adapter (session kind 9)

---

## 9. Summary

| Area | Approach | Key Dependency |
|------|----------|----------------|
| SSH terminal | Wrap existing ssh_ffi.spl | libssh2 FFI |
| Telnet terminal | New client on tcp.spl | RFC 854 IAC handling |
| T32 SWD serial | Trace32Client + window capture | Existing RCL protocol |
| Power (T32) | SYStem.Up/Down/RESetTarget via RCL | Trace32Client |
| Power (relay) | .shs script abstraction | Shell exec |
| Power (host PC) | WoL + SSH shutdown/reboot | ssh_ffi + UDP broadcast |
| Credentials | AES-CBC encrypted, master key file | AES + BCrypt libs |
| Remote test | SSH exec of `bin/simple test` | SSH terminal |
| Config | SDN format | Existing SDN parser |
| MCP | 17 new tools in lazy server | MCP tool registry |
