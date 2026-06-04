# Design: T32 Terminal, Power Control & Remote Test Runner

**Date:** 2026-03-29
**Status:** Draft
**Architecture:** `doc/04_architecture/t32_terminal_power_remote.md`
**Requirements:** `doc/02_requirements/feature/t32_terminal_power_remote.md`

---

## 1. Type Definitions

### 1.1 Terminal Types (`src/lib/nogc_sync_mut/terminal/types.spl`)

```simple
# Terminal kind constants
val TERM_KIND_SSH: i64 = 0
val TERM_KIND_TELNET: i64 = 1
val TERM_KIND_T32_SWD: i64 = 2
val TERM_KIND_RELAY: i64 = 3

# SSH auth mode constants
val SSH_AUTH_PASSWORD: i64 = 0
val SSH_AUTH_PUBKEY: i64 = 1
val SSH_AUTH_AGENT: i64 = 2

class TerminalConfig:
    name: text          # Config entry name (e.g., "test_host_ssh")
    kind: i64           # TERM_KIND_*
    host: text          # Hostname or IP
    port: i64           # Port number
    username: text      # Login username (empty if none)
    auth: i64           # SSH_AUTH_* (for SSH), ignored for others
    password: text      # Encrypted or plaintext password
    key_path: text      # SSH private key path (for pubkey auth)
    t32_host: text      # T32 API host (for T32_SWD kind)
    t32_port: i64       # T32 API port (for T32_SWD kind)
    channel: text       # T32 TERM channel (e.g., "TERM.A")
    poll_interval_ms: i64  # SWD poll interval (default 200)
    extra: Map<text, text> # Additional kind-specific parameters

class TerminalConnection:
    config: TerminalConfig
    connected: bool
    session_handle: i64    # Opaque handle (SSH session, TCP fd, etc.)
    last_output: text      # Last received output
    error: text            # Last error message (empty if none)

class TerminalExecResult:
    exit_code: i64
    stdout: text
    stderr: text
    duration_ms: i64
```

### 1.2 Power Types

```simple
# Power kind constants
val POWER_KIND_T32: i64 = 0
val POWER_KIND_RELAY: i64 = 1
val POWER_KIND_HOST: i64 = 2

# Power state constants
val POWER_STATE_UNKNOWN: i64 = 0
val POWER_STATE_ON: i64 = 1
val POWER_STATE_OFF: i64 = 2

class PowerConfig:
    name: text          # Config entry name (e.g., "t32_probe")
    kind: i64           # POWER_KIND_*
    t32_host: text      # T32 API host (for T32 kind)
    t32_port: i64       # T32 API port (for T32 kind)
    host: text          # Target host (for Host kind)
    ssh_port: i64       # SSH port (for Host kind)
    username: text      # SSH username (for Host kind)
    auth: i64           # SSH_AUTH_* (for Host kind)
    key_path: text      # SSH key path (for Host kind)
    password: text      # Encrypted password (for Host kind)
    mac: text           # MAC address for WoL (for Host kind)
    on_script: text     # Relay script paths
    off_script: text
    toggle_script: text
    reset_script: text
    state_script: text
    params: Map<text, text>  # Additional parameters

class PowerState:
    name: text          # Power target name
    kind: i64           # POWER_KIND_*
    state: i64          # POWER_STATE_*
    timestamp: i64      # Unix timestamp of query
    message: text       # Human-readable state description
```

---

## 2. SDN Configuration Format

### 2.1 Terminal Configuration

```sdn
terminals
  test_host_ssh
    kind: ssh
    host: 192.168.1.100
    port: 22
    username: testuser
    auth: password
    password: encrypted:aG9zdF9wYXNz...

  test_host_ssh_key
    kind: ssh
    host: 192.168.1.100
    port: 22
    username: testuser
    auth: pubkey
    key_path: ~/.ssh/id_ed25519

  device_telnet
    kind: telnet
    host: 192.168.1.200
    port: 23
    auth: none

  t32_swd_serial
    kind: t32_swd
    t32_host: localhost
    t32_port: 20000
    channel: TERM.A
    poll_interval_ms: 200
```

### 2.2 Power Configuration

```sdn
power
  t32_probe
    kind: t32
    t32_host: localhost
    t32_port: 20000

  board_relay
    kind: relay
    on_script: scripts/relay_on.shs
    off_script: scripts/relay_off.shs
    toggle_script: scripts/relay_toggle.shs
    reset_script: scripts/relay_reset.shs
    state_script: scripts/relay_state.shs

  test_host
    kind: host
    host: 192.168.1.100
    ssh_port: 22
    username: testuser
    auth: pubkey
    key_path: ~/.ssh/id_ed25519
    mac: AA:BB:CC:DD:EE:FF
```

---

## 3. Dispatch Logic

### 3.1 Terminal Connect

```simple
fn terminal_connect(config: TerminalConfig) -> Result<TerminalConnection, text>:
    match config.kind:
        TERM_KIND_SSH:
            ssh_terminal_connect(config)
        TERM_KIND_TELNET:
            telnet_terminal_connect(config)
        TERM_KIND_T32_SWD:
            t32_swd_terminal_connect(config)
        TERM_KIND_RELAY:
            relay_terminal_connect(config)
        _:
            Err("unknown terminal kind: {config.kind}")
```

### 3.2 Terminal Execute

```simple
fn terminal_execute(conn: TerminalConnection, command: text) -> Result<TerminalExecResult, text>:
    if not conn.connected:
        return Err("terminal not connected: {conn.config.name}")
    match conn.config.kind:
        TERM_KIND_SSH:
            ssh_terminal_execute(conn, command)
        TERM_KIND_TELNET:
            telnet_terminal_execute(conn, command)
        TERM_KIND_T32_SWD:
            t32_swd_terminal_execute(conn, command)
        TERM_KIND_RELAY:
            relay_terminal_execute(conn, command)
        _:
            Err("unknown terminal kind: {conn.config.kind}")
```

### 3.3 Power Control

```simple
fn power_on(config: PowerConfig) -> Result<text, text>:
    match config.kind:
        POWER_KIND_T32:
            t32_power_on(config)
        POWER_KIND_RELAY:
            relay_power_on(config)
        POWER_KIND_HOST:
            host_power_on(config)
        _:
            Err("unknown power kind: {config.kind}")

fn power_state(config: PowerConfig) -> Result<PowerState, text>:
    match config.kind:
        POWER_KIND_T32:
            t32_power_state(config)
        POWER_KIND_RELAY:
            relay_power_state(config)
        POWER_KIND_HOST:
            host_power_state(config)
        _:
            Err("unknown power kind: {config.kind}")
```

---

## 4. MCP Tool Schemas

### 4.1 Terminal Tools

**terminal_connect**
```
Input:  { "name": text }                    # Terminal config name
Output: { "connected": bool, "message": text }
```

**terminal_disconnect**
```
Input:  { "name": text }                    # Terminal config name
Output: { "disconnected": bool, "message": text }
```

**terminal_send**
```
Input:  { "name": text, "data": text }      # Terminal name + data to send
Output: { "sent": bool, "bytes": i64 }
```

**terminal_receive**
```
Input:  { "name": text, "timeout_ms": i64 } # Terminal name + read timeout
Output: { "data": text, "bytes": i64 }
```

**terminal_execute**
```
Input:  { "name": text, "command": text, "timeout_ms": i64 }
Output: { "exit_code": i64, "stdout": text, "stderr": text, "duration_ms": i64 }
```

**terminal_list**
```
Input:  {}
Output: { "terminals": [{ "name": text, "kind": text, "connected": bool, "host": text }] }
```

**terminal_status**
```
Input:  { "name": text }
Output: { "name": text, "kind": text, "connected": bool, "host": text, "port": i64, "error": text }
```

**terminal_upload**
```
Input:  { "name": text, "local_path": text, "remote_path": text }
Output: { "uploaded": bool, "bytes": i64, "message": text }
```

### 4.2 Power Tools

**power_on**
```
Input:  { "name": text }                    # Power config name
Output: { "success": bool, "state": text, "message": text }
```

**power_off**
```
Input:  { "name": text }
Output: { "success": bool, "state": text, "message": text }
```

**power_toggle**
```
Input:  { "name": text }
Output: { "success": bool, "state": text, "message": text }
```

**power_reset**
```
Input:  { "name": text }
Output: { "success": bool, "message": text }
```

**power_state**
```
Input:  { "name": text }
Output: { "name": text, "kind": text, "state": text, "message": text }
```

**relay_execute**
```
Input:  { "name": text, "script": text, "args": text }
Output: { "exit_code": i64, "stdout": text, "stderr": text }
```

### 4.3 Remote Test Tools

**remote_test_run**
```
Input:  { "terminal_name": text, "test_path": text, "timeout_ms": i64 }
Output: { "started": bool, "job_id": text, "message": text }
```

**remote_test_status**
```
Input:  { "job_id": text }
Output: { "status": text, "progress": text, "elapsed_ms": i64 }
```

**remote_test_collect**
```
Input:  { "job_id": text }
Output: { "exit_code": i64, "passed": i64, "failed": i64, "skipped": i64, "stdout": text, "stderr": text }
```

---

## 5. Credential Encryption Flow

### 5.1 Encryption

```
User runs: simple terminal encrypt-password
  1. Prompt for plaintext password
  2. Load master key from ~/.simple/credential_key
     - If not exists: generate 256-bit random key, write file with 0600 perms
  3. Derive AES-256 key via BCrypt KDF from master key
  4. Generate random 16-byte IV
  5. Encrypt plaintext with AES-CBC (PKCS7 padding)
  6. Encode IV + ciphertext as Base64
  7. Output: "encrypted:<base64>"
  8. User pastes into SDN config file
```

### 5.2 Decryption (at connection time)

```
credential_resolve(value: text) -> text:
  1. If value does not start with "encrypted:": return value as-is
  2. Strip "encrypted:" prefix
  3. Base64 decode -> IV (16 bytes) + ciphertext
  4. Load master key from ~/.simple/credential_key
  5. Derive AES-256 key via BCrypt KDF from master key
  6. Decrypt AES-CBC, strip PKCS7 padding
  7. Return plaintext
```

### 5.3 Key Functions

```simple
fn credential_encrypt(plaintext: text, key_path: text) -> text:
    # Returns "encrypted:<base64>"
    pass_todo

fn credential_decrypt(encrypted: text, key_path: text) -> text:
    # Returns plaintext
    pass_todo

fn credential_resolve(value: text) -> text:
    # Transparent: decrypt if encrypted, pass-through otherwise
    if value.starts_with("encrypted:"):
        val key_path = "~/.simple/credential_key"
        credential_decrypt(value, key_path)
    else:
        value
```

---

## 6. Shell Script Interface Contract

### 6.1 Relay .shs Script Requirements

Every relay control script must follow this contract:

```shs
#!/usr/bin/env bash
set -eu

# Script receives operation context as $1 (if needed)
# Perform the relay operation (vendor-specific commands here)

# Exit 0 on success, non-zero on failure
# State scripts: print "on" or "off" to stdout (exactly, no extra whitespace)
```

### 6.2 Example: USB Relay On Script

```shs
#!/usr/bin/env bash
set -eu

# Turn on USB relay channel 1
usbrelay BITFT_1=1

exit 0
```

### 6.3 Example: GPIO Relay State Script

```shs
#!/usr/bin/env bash
set -eu

# Read GPIO pin 17 state
val=$(cat /sys/class/gpio/gpio17/value)
if [ "$val" = "1" ]; then
    echo "on"
else
    echo "off"
fi
```

### 6.4 Execution Model

```simple
fn relay_execute_script(script_path: text, args: text) -> Result<TerminalExecResult, text>:
    # Validate script exists
    # Execute with 10s timeout
    # Parse exit code and stdout
    val result = rt_shell_exec(script_path, args, 10000)
    Ok(TerminalExecResult(
        exit_code: result.exit_code,
        stdout: result.stdout.trim(),
        stderr: result.stderr,
        duration_ms: result.duration_ms
    ))
```

---

## 7. Implementation Notes

### 7.1 SSH Terminal

- Wraps `ssh_ffi.spl` extern functions
- Password auth: `rt_ssh_connect(host, port, username, credential_resolve(password))`
- Key auth: `rt_ssh_connect_key(host, port, username, key_path)`
- Execute: `rt_ssh_exec(session, command)` returns stdout, stderr, exit code
- Upload: `rt_sftp_init(session)` then `rt_sftp_upload(sftp, local, remote)`
- Close: `rt_ssh_disconnect(session)`

### 7.2 Telnet Terminal

- New `telnet.spl` built on `tcp.spl` TcpStream
- IAC byte filtering on all received data
- Minimal option negotiation (SGA yes, ECHO no, reject others)
- Login via prompt detection (configurable patterns)
- Command execution: send command + CR, read until prompt detected

### 7.3 T32 SWD Serial Terminal

- Reuses `Trace32Client` for RCL connection
- Setup: send `TERM.GATE SWD` PRACTICE command
- Read: poll `t32_capture_window_text(client, channel)` at configured interval
- Write: send `TERM.Out "<data>"` PRACTICE command
- Channel configurable (default `TERM.A`)

### 7.4 MCP Global State

Terminal connections are held in module-level mutable state:

```simple
var TERMINAL_CONNECTIONS: List<TerminalConnection> = []

fn find_connection(name: text) -> Option<TerminalConnection>:
    TERMINAL_CONNECTIONS.find(\c: c.config.name == name)
```

This matches the existing MCP tool pattern where T32 client state is held globally.

### 7.5 Remote Test Adapter

Follows `hardware_adapter.spl` pattern:

```simple
val SESSION_KIND_REMOTE_PC: i64 = 9

fn remote_pc_adapter_start(config: RemotePcConfig) -> Result<text, text>:
    # 1. Optionally power on target
    # 2. Open terminal connection
    # 3. Verify connectivity (echo test)
    pass_todo

fn remote_pc_adapter_execute(conn: TerminalConnection, test_path: text) -> Result<TerminalExecResult, text>:
    terminal_execute(conn, "bin/simple test {test_path}")

fn remote_pc_adapter_health(conn: TerminalConnection) -> Result<bool, text>:
    val result = terminal_execute(conn, "echo ok")
    Ok(result?.stdout.trim() == "ok")
```
