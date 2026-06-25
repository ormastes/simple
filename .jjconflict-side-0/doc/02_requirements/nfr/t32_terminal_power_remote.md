# Non-Functional Requirements: T32 Terminal, Power Control & Remote Test Runner

**Date:** 2026-03-29
**Status:** Draft
**Feature Requirements:** `doc/02_requirements/feature/t32_terminal_power_remote.md`

---

## Performance

### NFR-PERF-001: Connection Timeout

All terminal connections (SSH, telnet, T32 RCL) shall complete or fail within 5 seconds.

- **Metric:** Time from `terminal_connect` call to connection established or error returned
- **SSH:** TCP connect + key exchange + authentication < 5s
- **Telnet:** TCP connect + option negotiation + login < 5s
- **T32 RCL:** TCP connect to T32 API port < 5s
- **Rationale:** Interactive MCP tool usage requires responsive feedback. A 5s timeout prevents indefinite hangs when targets are unreachable.
- **Verification:** System test with unreachable host verifies timeout fires within 5-6s.

### NFR-PERF-002: T32 SWD Serial Poll Interval

The T32 SWD serial terminal shall poll for new data at intervals no shorter than 200ms.

- **Metric:** Minimum time between consecutive `t32_capture_window_text` calls
- **Rationale:** Polling too frequently overloads the T32 RCL connection and can interfere with active debug sessions. 200ms provides near-real-time terminal output without degrading probe performance.
- **Default:** 200ms (configurable upward via `poll_interval_ms` in SDN config)
- **Verification:** Timing measurement in system test confirms interval >= 200ms.

---

## Security

### NFR-SEC-001: Encrypted Password Storage

All passwords stored in SDN configuration files shall be encrypted at rest.

- **Format:** `encrypted:<base64-encoded-ciphertext>`
- **Algorithm:** AES-CBC with 256-bit key derived via BCrypt KDF
- **Plaintext passwords shall never appear in config files** committed to version control
- **Runtime behavior:** `credential_resolve()` transparently decrypts encrypted values and passes through plaintext values (for development convenience)
- **Rationale:** Config files may be shared or committed. Encrypted storage prevents credential leakage.
- **Verification:** System test encrypts a password, writes to config, reads back, decrypts, and confirms round-trip correctness.

### NFR-SEC-002: Master Key File Permissions

The master key file at `~/.simple/credential_key` shall have file permissions 0600 (owner read/write only).

- **Location:** `~/.simple/credential_key`
- **Permissions:** `0600` (Unix) -- owner read/write, no group or other access
- **Creation:** If the key file does not exist, `credential_encrypt` shall generate a random 256-bit key and create the file with correct permissions
- **Rationale:** The master key protects all encrypted credentials. Restrictive permissions prevent other users on the system from reading it.
- **Verification:** System test creates key file and verifies permissions via `stat`.

---

## Reliability

### NFR-REL-001: Shell Script Contract for Relay Control

All `.shs` relay control scripts shall follow a strict execution contract.

- **Header:** Must include `set -eu` (exit on error, undefined variable is error)
- **Exit codes:** 0 = success, non-zero = failure
- **State output:** State query scripts print exactly "on" or "off" to stdout (no trailing whitespace, no extra lines)
- **Timeout:** Script execution shall timeout after 10 seconds
- **Arguments:** Operations passed as `$1` if the script handles multiple operations
- **Error output:** Diagnostic messages to stderr (not parsed by the system)
- **Rationale:** A strict contract ensures predictable behavior across different relay hardware and user-provided scripts. `set -eu` catches common scripting errors early.
- **Verification:** System test with mock scripts verifies exit code handling, stdout parsing, and timeout behavior.

---

## Compatibility

### NFR-COMPAT-001: Coexistence with Existing T32 MCP Tools

The 17 new MCP tools shall coexist with the existing 36 T32 MCP tools without conflicts.

- **Tool naming:** New tools use `terminal_`, `power_`, `relay_`, and `remote_test_` prefixes to avoid name collisions with existing `t32_` prefixed tools
- **Lazy loading:** New tool handlers loaded lazily (same pattern as existing tools) to avoid startup cost when not used
- **Configuration:** Terminal/power config is separate from existing T32 config (`config/t32/t32_terminal.sdn` vs existing T32 config files)
- **Shared resources:** T32 SWD terminal and T32 power controller share the Trace32Client connection with existing T32 tools. Connection multiplexing must not interfere with debug operations.
- **Rationale:** Users with existing T32 MCP setups must not experience regressions.
- **Verification:** System test initializes both old and new tool sets and verifies all 53 tools are registered without conflicts.

---

## Summary

| NFR ID | Category | Key Metric | Threshold |
|--------|----------|------------|-----------|
| NFR-PERF-001 | Performance | Connection timeout | < 5 seconds |
| NFR-PERF-002 | Performance | SWD poll interval | >= 200ms |
| NFR-SEC-001 | Security | Password storage | AES-CBC encrypted |
| NFR-SEC-002 | Security | Key file permissions | 0600 |
| NFR-REL-001 | Reliability | Script contract | set -eu, exit 0/1, stdout state |
| NFR-COMPAT-001 | Compatibility | Tool coexistence | 36 existing + 17 new = 53 tools |
