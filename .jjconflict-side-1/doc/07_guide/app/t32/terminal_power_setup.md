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

### 4.1 USB HID Relay (usbrelay)

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

### 4.2 Arduino Serial Relay (USB-Serial)

For relay boards that use Arduino-style serial communication (CH340, CP2102, or native Arduino USB). These appear as `/dev/ttyACM*` or `/dev/ttyUSB*`.

```
                 USB (serial)
  Host PC  ==================  Arduino/CH340 Relay Board
                                  |
                                  | Relay contacts (NO/NC/COM)
                                  |
                            +-----+------+
                            |            |
                          Power        Device
                          Supply       Under Test
```

#### Device Detection

The included relay scripts auto-detect the device. Detection priority:

1. **`RELAY_DEVICE` env var** (explicit override)
2. **USB VID:PID** via `lsusb` + sysfs (configurable: `RELAY_USB_VID`, `RELAY_USB_PID`)
3. **Fallback**: first `/dev/ttyACM*` or `/dev/ttyUSB*`

Find your device manually:

```bash
# List serial devices
ls /dev/ttyACM* /dev/ttyUSB* 2>/dev/null

# Find USB vendor/product ID
lsusb | grep -i ch340    # CH340 chips: 1a86:7523
lsusb | grep -i cp210    # CP2102 chips: 10c4:ea60
lsusb | grep -i arduino  # Arduino Uno: 2341:0043
```

#### Environment Variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `RELAY_DEVICE` | (auto) | Explicit device path, e.g. `/dev/ttyACM0` |
| `RELAY_USB_VID` | `1a86` | USB vendor ID (CH340 default) |
| `RELAY_USB_PID` | `7523` | USB product ID (CH340 default) |
| `RELAY_BAUD` | `9600` | Serial baud rate |
| `RELAY_CMD_ON` | `ON` | Serial command for relay ON |
| `RELAY_CMD_OFF` | `OFF` | Serial command for relay OFF |
| `RELAY_CMD_STATE` | `STATE` | Serial command to query state |
| `RELAY_CMD_TOGGLE` | `TOGGLE` | Serial command to toggle |
| `RELAY_RESET_DELAY` | `2` | Seconds between off/on during reset |

#### Quick Start

```bash
# 1. Plug in the relay board
# 2. Check it appeared
ls /dev/ttyACM* /dev/ttyUSB*

# 3. Ensure permissions (add yourself to dialout group)
sudo usermod -aG dialout $USER
# Log out and back in for group change to take effect

# 4. Test directly
RELAY_DEVICE=/dev/ttyACM0 scripts/relay_state.shs   # prints "on" or "off"
RELAY_DEVICE=/dev/ttyACM0 scripts/relay_off.shs      # relay clicks, board powers off
RELAY_DEVICE=/dev/ttyACM0 scripts/relay_on.shs       # relay clicks, board powers on

# 5. Use via power control (reads config from config/t32/t32_terminal.sdn)
bin/simple power state board_power
bin/simple power off board_power
bin/simple power on board_power
bin/simple power reset board_power   # off -> 2s delay -> on
```

#### Custom Protocols

If your relay firmware uses non-standard commands (e.g. hex bytes, different keywords), override via environment variables:

```bash
# Example: relay that uses "RELAY_SET 1" / "RELAY_SET 0" / "RELAY_GET"
export RELAY_CMD_ON="RELAY_SET 1"
export RELAY_CMD_OFF="RELAY_SET 0"
export RELAY_CMD_STATE="RELAY_GET"
export RELAY_BAUD=115200
```

### 4.3 Arduino Relay Firmware Requirements

The relay scripts expect a simple text serial protocol at 9600 baud (configurable):

| Command | Expected Response | Meaning |
|---------|-------------------|---------|
| `ON\n` | `OK` or none | Close relay (power on) |
| `OFF\n` | `OK` or none | Open relay (power off) |
| `STATE\n` | `ON` or `OFF` | Query current state |
| `TOGGLE\n` | `OK` or none | Flip current state |

Minimal Arduino sketch for reference:

```cpp
const int RELAY_PIN = 7;
bool relayOn = true;  // default ON (normally closed)

void setup() {
    Serial.begin(9600);
    pinMode(RELAY_PIN, OUTPUT);
    digitalWrite(RELAY_PIN, HIGH);
}

void loop() {
    if (Serial.available()) {
        String cmd = Serial.readStringUntil('\n');
        cmd.trim();
        if (cmd == "ON")       { relayOn = true;  digitalWrite(RELAY_PIN, HIGH); Serial.println("OK"); }
        else if (cmd == "OFF") { relayOn = false; digitalWrite(RELAY_PIN, LOW);  Serial.println("OK"); }
        else if (cmd == "STATE")  { Serial.println(relayOn ? "ON" : "OFF"); }
        else if (cmd == "TOGGLE") { relayOn = !relayOn; digitalWrite(RELAY_PIN, relayOn ? HIGH : LOW); Serial.println("OK"); }
    }
}
```

Test the firmware interactively:

```bash
screen /dev/ttyACM0 9600
# Type: STATE<Enter> — should see ON or OFF
# Ctrl-A, K, Y to exit screen
```

### 4.4 Troubleshooting Serial Relay

| Problem | Cause | Solution |
|---------|-------|----------|
| "Permission denied" | Not in dialout group | `sudo usermod -aG dialout $USER`, re-login |
| "No USB relay device found" | Device not plugged in or wrong VID:PID | Check `lsusb`, set `RELAY_USB_VID`/`RELAY_USB_PID` |
| No response from relay | Wrong baud rate | Set `RELAY_BAUD` to match firmware (try 9600, 115200) |
| Relay resets on script run | Arduino DTR reset on serial open | Scripts use `stty -hupcl` to prevent this |
| Wrong device picked | Multiple serial devices | Set `RELAY_DEVICE=/dev/ttyACMN` explicitly |
| "could not acquire lock" | Another script holds the port | Wait or check for stuck processes |
| macOS: device not found | Different device naming | Use `/dev/cu.usbmodem*` or `/dev/cu.usbserial*` |

### 4.5 Create Custom Relay Scripts

If the included scripts (`scripts/relay_on.shs`, etc.) don't fit your hardware, create custom ones following this contract:

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
