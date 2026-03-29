# Guide: Terminal, Power Control & Remote Test Runner Setup

**Date:** 2026-03-29
**Design:** `doc/05_design/t32_terminal_power_remote.md`

---

## 1. SSH Terminal Setup

### 1.1 Password Authentication

1. Ensure the remote host has SSH enabled (port 22 or custom).
2. Encrypt the password:

```bash
bin/simple terminal encrypt-password
# Enter password when prompted
# Output: encrypted:aG9zdF9wYXNz...
```

3. Add to `config/t32/t32_terminal.sdn`:

```sdn
terminals
  my_host
    kind: ssh
    host: 192.168.1.100
    port: 22
    username: testuser
    auth: password
    password: encrypted:aG9zdF9wYXNz...
```

4. Test the connection:

```bash
bin/simple terminal connect my_host
bin/simple terminal exec my_host "echo hello"
```

### 1.2 Key-Based Authentication

1. Generate an SSH key pair (if you don't have one):

```bash
ssh-keygen -t ed25519 -f ~/.ssh/id_ed25519
```

2. Copy the public key to the remote host:

```bash
ssh-copy-id -i ~/.ssh/id_ed25519.pub testuser@192.168.1.100
```

3. Add to `config/t32/t32_terminal.sdn`:

```sdn
terminals
  my_host_key
    kind: ssh
    host: 192.168.1.100
    port: 22
    username: testuser
    auth: pubkey
    key_path: ~/.ssh/id_ed25519
```

4. Test the connection:

```bash
bin/simple terminal connect my_host_key
bin/simple terminal exec my_host_key "uname -a"
```

---

## 2. Telnet Terminal Setup

### 2.1 With Authentication

1. Ensure the target device has a telnet server running.
2. Add to `config/t32/t32_terminal.sdn`:

```sdn
terminals
  device_telnet
    kind: telnet
    host: 192.168.1.200
    port: 23
    username: admin
    password: encrypted:ZGV2aWNlX3Bhc3M...
```

3. Test:

```bash
bin/simple terminal connect device_telnet
bin/simple terminal exec device_telnet "show version"
```

### 2.2 Without Authentication

For devices that drop directly to a shell prompt:

```sdn
terminals
  device_telnet_noauth
    kind: telnet
    host: 192.168.1.200
    port: 23
    auth: none
```

### 2.3 Security Warning

Telnet transmits all data in plaintext. Use only on isolated lab networks. Prefer SSH whenever possible.

---

## 3. T32 SWD Serial Terminal

### 3.1 Prerequisites

- TRACE32 PowerView running with an active SWD connection to the target
- T32 API (Remote Control) enabled on a known port (default: 20000)
- Target firmware configured to use SWD terminal output

### 3.2 Enable TERM Window in TRACE32

Run these PRACTICE commands in TRACE32 PowerView (or add to your startup script):

```practice
; Enable SWD terminal gate
TERM.GATE SWD

; Alternative: use TERM.Method
; TERM.Method SWD

; Open the TERM window
TERM.view

; Optionally set terminal parameters
TERM.SIZE 80. 24.
```

### 3.3 Configure in SDN

```sdn
terminals
  t32_swd_serial
    kind: t32_swd
    t32_host: localhost
    t32_port: 20000
    channel: TERM.A
    poll_interval_ms: 200
```

- `t32_host` / `t32_port`: Must match your T32 PowerView API settings
- `channel`: The TERM window name. Use `TERM.A` for the first window, `TERM.B` for a second, etc.
- `poll_interval_ms`: How often to poll for new output. Minimum 200ms. Increase if you see T32 performance degradation.

### 3.4 Usage

```bash
# Connect and read terminal output
bin/simple terminal connect t32_swd_serial

# Send data to target
bin/simple terminal exec t32_swd_serial "hello target"

# Read current terminal buffer
bin/simple terminal exec t32_swd_serial ""
```

### 3.5 Troubleshooting T32 SWD Terminal

- **"Connection refused"**: Verify T32 API is enabled. Check `RCL=NETTCP` in your T32 config.
- **No output**: Verify target firmware writes to SWD terminal. Check `TERM.GATE SWD` is active.
- **Garbled output**: Check baud rate settings if using TERM.Method with UART. SWD does not need baud rate.
- **Slow response**: Increase `poll_interval_ms` if T32 is busy with debug operations.

---

## 4. Relay Wiring Guide

### 4.1 USB Relay Board Connection

Common setup with a USB HID relay module:

```
                 USB
  Host PC  ============  USB Relay Board
                           |
                           | Relay contacts (NO/NC/COM)
                           |
                     +-----+------+
                     |            |
                   Power        Device
                   Supply       Under Test
```

1. Connect the USB relay board to your host PC.
2. Install relay control software (e.g., `usbrelay` for HID relays).
3. Identify the relay ID:

```bash
usbrelay
# Output: BITFT_1=0  BITFT_2=0
```

4. Wire the relay:
   - **COM** (common) to power supply positive
   - **NO** (normally open) to device power input
   - When relay energizes, circuit closes and device powers on

### 4.2 GPIO Relay Connection (Raspberry Pi)

```
  Raspberry Pi GPIO 17  ---[1k resistor]--- Relay module IN
  Raspberry Pi GND      ------------------- Relay module GND
  Raspberry Pi 5V       ------------------- Relay module VCC
```

### 4.3 Create Relay Scripts

Create `.shs` scripts for each operation. All scripts must use `set -eu` and exit 0 on success.

**scripts/relay_on.shs:**
```shs
#!/usr/bin/env bash
set -eu
usbrelay BITFT_1=1
exit 0
```

**scripts/relay_off.shs:**
```shs
#!/usr/bin/env bash
set -eu
usbrelay BITFT_1=0
exit 0
```

**scripts/relay_state.shs:**
```shs
#!/usr/bin/env bash
set -eu
state=$(usbrelay BITFT_1 2>/dev/null | grep -o '[01]$')
if [ "$state" = "1" ]; then
    echo "on"
else
    echo "off"
fi
```

**scripts/relay_reset.shs:**
```shs
#!/usr/bin/env bash
set -eu
usbrelay BITFT_1=0
sleep 2
usbrelay BITFT_1=1
exit 0
```

5. Make scripts executable:

```bash
chmod +x scripts/relay_*.shs
```

---

## 5. Power Control Configuration

### 5.1 T32 Probe Power

Controls target power via T32 debug probe SYStem commands.

```sdn
power
  t32_probe
    kind: t32
    t32_host: localhost
    t32_port: 20000
```

Usage:
```bash
bin/simple power on t32_probe      # SYStem.Up
bin/simple power off t32_probe     # SYStem.Down
bin/simple power reset t32_probe   # SYStem.RESetTarget
bin/simple power state t32_probe   # STATE.RUN() query
```

### 5.2 Relay Power

Controls power via relay scripts (see section 4).

```sdn
power
  board_relay
    kind: relay
    on_script: scripts/relay_on.shs
    off_script: scripts/relay_off.shs
    toggle_script: scripts/relay_toggle.shs
    reset_script: scripts/relay_reset.shs
    state_script: scripts/relay_state.shs
```

### 5.3 Host PC Power

Controls a remote PC via Wake-on-LAN (power on) and SSH (shutdown/reboot).

```sdn
power
  test_host
    kind: host
    host: 192.168.1.100
    ssh_port: 22
    username: testuser
    auth: pubkey
    key_path: ~/.ssh/id_ed25519
    mac: AA:BB:CC:DD:EE:FF
```

- `mac`: Required for Wake-on-LAN. Find with `ip link show` on the target.
- WoL must be enabled in the target's BIOS and OS network driver.

Usage:
```bash
bin/simple power on test_host      # Wake-on-LAN magic packet
bin/simple power off test_host     # SSH: shutdown -h now
bin/simple power reset test_host   # SSH: reboot
bin/simple power state test_host   # TCP probe SSH port
```

---

## 6. Remote Test Runner Setup

### 6.1 Prerequisites

- A remote host with `bin/simple` installed and accessible
- SSH terminal configured (see section 1)
- Test files present on the remote host (or uploaded via SFTP)

### 6.2 Configuration

The remote test runner uses an existing terminal connection. No additional config is needed beyond the terminal entry.

### 6.3 Running Remote Tests

```bash
# Run a single test file on a remote host
bin/simple remote-test my_host test/lib/common/text_spec.spl

# The command will:
# 1. Connect to my_host via SSH
# 2. Execute: bin/simple test test/lib/common/text_spec.spl
# 3. Collect stdout/stderr and exit code
# 4. Display results locally
```

### 6.4 With Power Control

If you need to power on the host before testing:

```bash
bin/simple power on test_host
# Wait for boot...
bin/simple power state test_host    # Verify: "on"
bin/simple remote-test my_host_key test/lib/common/text_spec.spl
```

### 6.5 MCP Usage

When using via MCP tools in Claude Code or other AI assistants:

```
1. terminal_connect(name: "my_host")
2. remote_test_run(terminal_name: "my_host", test_path: "test/lib/common/text_spec.spl")
3. remote_test_status(job_id: "<returned job_id>")
4. remote_test_collect(job_id: "<returned job_id>")
5. terminal_disconnect(name: "my_host")
```

---

## 7. Credential Encryption

### 7.1 How It Works

Passwords in SDN config are stored encrypted using AES-CBC with a local master key.

- Master key location: `~/.simple/credential_key`
- Key permissions: `0600` (owner read/write only)
- Encrypted format: `encrypted:<base64(IV + ciphertext)>`

### 7.2 Encrypting a Password

```bash
bin/simple terminal encrypt-password
# Prompts: Enter password:
# Output:  encrypted:c2FsdGVkX1+abc123def456...

# Copy the output into your SDN config file
```

### 7.3 Master Key Management

The master key is generated automatically on first encryption. To manage it:

- **Backup:** Copy `~/.simple/credential_key` to a secure location.
- **Rotate:** Delete the key file and re-encrypt all passwords. Old encrypted values become unrecoverable.
- **Share:** To use the same config on multiple machines, copy the key file (securely) to each machine.

### 7.4 Verifying Permissions

```bash
ls -la ~/.simple/credential_key
# Expected: -rw------- 1 user user 32 ... credential_key
```

If permissions are wrong:

```bash
chmod 0600 ~/.simple/credential_key
```

---

## 8. Complete Example SDN Config

```sdn
# config/t32/t32_terminal.sdn
# Terminal and power control configuration

terminals
  # SSH with password auth
  lab_pc
    kind: ssh
    host: 192.168.1.100
    port: 22
    username: testuser
    auth: password
    password: encrypted:c2FsdGVkX1+abc123...

  # SSH with key auth
  lab_pc_key
    kind: ssh
    host: 192.168.1.100
    port: 22
    username: testuser
    auth: pubkey
    key_path: ~/.ssh/id_ed25519

  # Telnet to embedded device
  target_console
    kind: telnet
    host: 192.168.1.200
    port: 23
    auth: none

  # T32 SWD serial
  target_swd
    kind: t32_swd
    t32_host: localhost
    t32_port: 20000
    channel: TERM.A
    poll_interval_ms: 200

power
  # T32 probe power
  t32_target
    kind: t32
    t32_host: localhost
    t32_port: 20000

  # USB relay for board power
  board_power
    kind: relay
    on_script: scripts/relay_on.shs
    off_script: scripts/relay_off.shs
    toggle_script: scripts/relay_toggle.shs
    reset_script: scripts/relay_reset.shs
    state_script: scripts/relay_state.shs

  # Lab PC power (WoL + SSH)
  lab_pc_power
    kind: host
    host: 192.168.1.100
    ssh_port: 22
    username: testuser
    auth: pubkey
    key_path: ~/.ssh/id_ed25519
    mac: AA:BB:CC:DD:EE:FF
```

---

## 9. Troubleshooting

### SSH Issues

| Problem | Cause | Solution |
|---------|-------|----------|
| "Connection refused" | SSH server not running | Start sshd on remote host |
| "Authentication failed" | Wrong credentials | Verify username/password, check key path |
| "Permission denied (publickey)" | Key not in authorized_keys | Run `ssh-copy-id` to install public key |
| "Connection timed out" | Network unreachable | Check IP, firewall rules, ping target |
| "Encrypted password failed" | Wrong master key | Verify `~/.simple/credential_key` matches |

### Telnet Issues

| Problem | Cause | Solution |
|---------|-------|----------|
| "Connection refused" | Telnet server not running | Enable telnetd on target |
| "Login failed" | Prompt pattern mismatch | Check if device uses non-standard prompts |
| Garbled output | IAC handling error | Verify telnet (not raw TCP) on target port |

### T32 SWD Issues

| Problem | Cause | Solution |
|---------|-------|----------|
| "Connection refused" | T32 API not enabled | Add `RCL=NETTCP` to T32 config, restart |
| "No terminal output" | TERM.GATE not set | Run `TERM.GATE SWD` in T32 |
| "Wrong channel" | Channel mismatch | Check `channel` in config matches T32 window |
| Slow polling | Interval too low | Increase `poll_interval_ms` (min 200) |

### Power Control Issues

| Problem | Cause | Solution |
|---------|-------|----------|
| WoL not working | WoL disabled in BIOS | Enable WoL in BIOS and OS NIC driver |
| WoL wrong MAC | MAC mismatch | Verify MAC with `ip link show` on target |
| Relay script fails | Permission denied | Run `chmod +x` on .shs scripts |
| Relay state wrong | Script output format | Ensure state script prints only "on" or "off" |
| T32 power fails | Target not connected | Verify SWD connection in T32 PowerView |

### Credential Issues

| Problem | Cause | Solution |
|---------|-------|----------|
| "Key file not found" | Missing master key | Run `encrypt-password` to generate key |
| "Decryption failed" | Corrupted key or data | Re-encrypt the password with current key |
| "Permission denied" | Key file permissions | Run `chmod 0600 ~/.simple/credential_key` |
