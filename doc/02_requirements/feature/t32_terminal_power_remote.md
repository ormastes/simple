# Requirements: T32 Terminal, Power Control & Remote Test Runner

**Date:** 2026-03-29
**Status:** Draft
**Research:** `doc/01_research/domain/t32_terminal_power_remote_2026-03-29.md`

---

## 1. Terminal Requirements

### REQ-TERM-001: SSH Terminal with Password Authentication

The system shall provide SSH terminal connectivity using password-based authentication.

- Connect to remote host via SSH (TCP port, configurable)
- Authenticate with username and password
- Passwords stored in SDN config shall be encrypted (see REQ-CFG-002)
- Decrypt password at connection time using master key
- Support exec channel for single command execution
- Return exit code, stdout, and stderr from executed commands
- **Depends on:** `src/lib/nogc_sync_mut/io/ssh_ffi.spl` (`rt_ssh_connect`)

### REQ-TERM-002: SSH Terminal with Key-Based Authentication

The system shall provide SSH terminal connectivity using public key authentication.

- Authenticate with username and private key file path
- Support Ed25519, RSA, and ECDSA key types
- Private key path configurable in SDN config
- Passphrase-protected keys: passphrase treated as a credential (encrypted storage)
- **Depends on:** `src/lib/nogc_sync_mut/io/ssh_ffi.spl` (`rt_ssh_connect_key`)

### REQ-TERM-003: Telnet Terminal with Optional Authentication

The system shall provide telnet terminal connectivity.

- Connect to remote host via TCP (default port 23, configurable)
- Handle IAC byte (0xFF) in-band commands per RFC 854
- Negotiate minimal option set: WILL SGA, WONT ECHO
- Optional login: detect "login:"/"Username:" and "Password:" prompts
- Support `auth: none` for unauthenticated connections
- Send commands and receive responses with configurable prompt detection
- **Depends on:** `src/lib/nogc_sync_mut/net/tcp.spl` (TcpStream)

### REQ-TERM-004: T32 SWD Serial Terminal via TERM Window

The system shall provide terminal access to target devices through T32's SWD serial debug channel.

- Connect to TRACE32 via RCL (existing Trace32Client)
- Configure TERM window: `TERM.GATE SWD` or `TERM.Method SWD`
- Read terminal output via `t32_capture_window_text(client, channel)`
- Write to terminal via `TERM.Out <data>` PRACTICE command
- Poll-based reading with configurable interval (minimum 200ms)
- Support multiple channels: `TERM.A`, `TERM.B`, etc.
- **Depends on:** `src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl`, `t32_window_capture.spl`

### REQ-TERM-005: Unified Terminal Interface

The system shall provide a consistent interface across all terminal types.

- Common operations: `connect`, `send`, `receive`, `execute`, `close`
- Dispatch by terminal kind (SSH=0, Telnet=1, T32_SWD=2, Relay=3)
- `execute` returns `TerminalExecResult` with exit_code, stdout, stderr
- `connect` returns `TerminalConnection` with connection state
- Kind-based dispatch (no inheritance, per project rules)
- All terminal types configured via SDN (see REQ-CFG-001)

---

## 2. Power Control Requirements

### REQ-PWR-001: T32 Power On/Off/Reset via SYStem Commands

The system shall control target power through T32 debug probe commands.

- `power_on` -> execute `SYStem.Up` via Trace32Client
- `power_off` -> execute `SYStem.Down` via Trace32Client
- `reset` -> execute `SYStem.RESetTarget` via Trace32Client
- `power_state` -> execute `EVAL STATE.RUN()` and parse result
- `power_toggle` -> not supported (return error)
- **Depends on:** `src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl`

### REQ-PWR-002: Relay Power Control via .shs Scripts

The system shall control power through relay hardware using configurable shell scripts.

- Each power operation maps to a `.shs` script path from config
- Scripts: `on_script`, `off_script`, `toggle_script`, `reset_script`, `state_script`
- Script contract:
  - Must use `set -eu` for safety
  - Exit 0 = success, non-zero = failure
  - `state_script` prints "on" or "off" to stdout
  - Arguments passed as `$1` if needed
- Execute via `rt_shell_exec` (shell execution FFI)
- **Depends on:** Shell execution runtime

### REQ-PWR-003: Host PC Power Control

The system shall control host PC power using network protocols.

- `power_on` -> Send Wake-on-LAN magic packet (UDP broadcast, requires MAC address in config)
- `power_off` -> SSH execute `shutdown -h now` on target host
- `reset` -> SSH execute `reboot` on target host
- `power_state` -> TCP connect to SSH port; success = on, timeout = off
- `power_toggle` -> Query state, then execute on or off accordingly
- **Depends on:** SSH terminal (REQ-TERM-001 or REQ-TERM-002), UDP socket

### REQ-PWR-004: Consistent Power Interface

The system shall provide a uniform power control interface across all controller types.

- Five operations: `power_on`, `power_off`, `power_toggle`, `reset`, `power_state`
- Each power target declares which operations it supports
- Unsupported operations return a clear error
- Dispatch by power kind (T32, Relay, Host)
- Kind-based dispatch (no inheritance)

### REQ-PWR-005: Power State Query

The system shall report the current power state of managed targets.

- States: `unknown` (0), `on` (1), `off` (2)
- T32: derived from `STATE.RUN()` evaluation
- Relay: derived from `state_script` stdout
- Host: derived from SSH port probe (TCP connect with timeout)
- Return `PowerState` struct with kind, name, state value, and timestamp

---

## 3. Remote Test Requirements

### REQ-REM-001: Remote Test Execution via SSH/Telnet

The system shall execute test suites on remote hosts via terminal connections.

- Upload test files to remote host if needed (SFTP for SSH)
- Execute `bin/simple test <path>` on remote host via terminal exec
- Support SSH and telnet as transport
- Use existing SessionAdapter pattern (add session kind 9: REMOTE_PC)
- **Depends on:** REQ-TERM-001 or REQ-TERM-002 or REQ-TERM-003

### REQ-REM-002: Remote Test Result Collection

The system shall collect and parse test results from remote execution.

- Capture stdout/stderr from remote `bin/simple test` execution
- Parse test result summary (passed, failed, skipped counts)
- Return structured `TerminalExecResult` with exit code and output
- Timeout configurable per remote test execution

---

## 4. Configuration Requirements

### REQ-CFG-001: SDN Configuration for Terminals and Power

The system shall use SDN format for all terminal and power configuration.

- Config file: `config/t32/t32_terminal.sdn`
- Terminal section: `terminals` block with named entries
- Power section: `power` block with named entries
- Each entry specifies `kind` and kind-specific parameters
- Named entries allow CLI and MCP tools to reference by name (e.g., `test_host_ssh`)

### REQ-CFG-002: Credential Encryption with AES-CBC

The system shall encrypt sensitive credentials stored in SDN config.

- Encrypted values prefixed with `encrypted:` followed by Base64-encoded ciphertext
- Encryption: `credential_encrypt(plaintext, key_path)` -> `"encrypted:<base64>"`
- Decryption: `credential_decrypt(encrypted, key_path)` -> plaintext
- Resolution: `credential_resolve(value)` -- transparently decrypts if prefixed, returns as-is otherwise
- Master key file: `~/.simple/credential_key` with 0600 permissions
- Uses AES-CBC from `src/lib/common/aes/` and BCrypt KDF from `src/lib/common/bcrypt/key_derivation.spl`

---

## 5. MCP Tool Requirements

### REQ-MCP-001: 17 New MCP Tools

The system shall expose 17 new MCP tools in the Simple MCP server.

**Terminal tools (8):**

| Tool | Description |
|------|-------------|
| `terminal_connect` | Open terminal connection by config name |
| `terminal_disconnect` | Close terminal connection |
| `terminal_send` | Send data to connected terminal |
| `terminal_receive` | Receive data from connected terminal |
| `terminal_execute` | Execute command and return result |
| `terminal_list` | List configured terminals and their status |
| `terminal_status` | Get status of a specific terminal connection |
| `terminal_upload` | Upload file to remote host (SSH/SFTP only) |

**Power tools (6):**

| Tool | Description |
|------|-------------|
| `power_on` | Power on target by config name |
| `power_off` | Power off target by config name |
| `power_toggle` | Toggle power state |
| `power_reset` | Reset target |
| `power_state` | Query current power state |
| `relay_execute` | Execute arbitrary relay script |

**Remote test tools (3):**

| Tool | Description |
|------|-------------|
| `remote_test_run` | Run test suite on remote host |
| `remote_test_status` | Check status of running remote test |
| `remote_test_collect` | Collect results of completed remote test |

- All tools integrate with existing MCP lazy server (`src/lib/nogc_async_mut/mcp/main_lazy.spl`)
- Tool schemas defined in `src/lib/nogc_async_mut/mcp/main_lazy_protocol.spl`
- Tool table entries in `src/app/mcp/tool_table.spl`
- Must coexist with existing 36 T32 MCP tools (see NFR-COMPAT-001)

---

## Traceability

| Requirement | Test Coverage | Design Section |
|-------------|---------------|----------------|
| REQ-TERM-001 | SSH password connect/execute | SSH terminal |
| REQ-TERM-002 | SSH key connect/execute | SSH terminal |
| REQ-TERM-003 | Telnet connect/command | Telnet terminal |
| REQ-TERM-004 | T32 SWD read/write | T32 SWD terminal |
| REQ-TERM-005 | Dispatch routing | Connection dispatch |
| REQ-PWR-001 | T32 power on/off/reset/state | T32 power |
| REQ-PWR-002 | Relay script execution | Relay power |
| REQ-PWR-003 | Host WoL/shutdown/reboot | Host power |
| REQ-PWR-004 | Dispatch routing | Power controller |
| REQ-PWR-005 | State query all types | Power state |
| REQ-REM-001 | Remote SSH test run | Remote test runner |
| REQ-REM-002 | Result parsing | Remote test collect |
| REQ-CFG-001 | SDN config parsing | Config parser |
| REQ-CFG-002 | Encrypt/decrypt round-trip | Credential store |
| REQ-MCP-001 | MCP tool dispatch (17 tools) | MCP tool handlers |
