# RISC-V 64 FPGA Hardware Inventory — 2026-05-19

**Board:** ML_Carrier_Card (Xilinx/AMD Kria K26 / XCZU5EV carrier)
**Date:** 2026-05-19
**Operator:** ormastes

---

## 1. Board Identification

| Field          | Value                                         |
|----------------|-----------------------------------------------|
| Board Model    | ML_Carrier_Card (Xilinx/AMD)                  |
| FPGA           | Kria K26 (XCZU5EV Zynq UltraScale+ MPSoC)     |
| USB Device     | 0403:6011 (Future Technology Devices FT4232H) |
| USB Serial     | XFL1OSWWFM2B                                  |
| USB Path       | 3-2 (interfaces 0–3)                          |
| Host Interface | USB-A → board micro-USB                       |

---

## 2. FT4232H Channel Map

The FT4232H presents 4 UART/MPSSE interfaces. Xilinx ML Carrier Card assignment:

| Channel | bInterfaceNumber | USB Sysfs Path | ttyUSB      | Function                  | Baud   |
|---------|-----------------|----------------|-------------|---------------------------|--------|
| A       | 0               | 3-2:1.0        | (none/JTAG) | JTAG MPSSE                | N/A    |
| B       | 1               | 3-2:1.1        | ttyUSB2     | Console UART (PS UART0)   | 115200 |
| C       | 2               | 3-2:1.2        | ttyUSB3     | UART1 / PL UART           | 115200 |
| D       | 3               | 3-2:1.3        | ttyUSB5     | Spare / Platform          | 115200 |

**Notes:**
- Channel A (JTAG) is NOT enumerated as ttyUSB when `ftdi_sio` claims all 4 interfaces.
- For JTAG operations, interface 0 (`3-2:1.0`) must be unbound from `ftdi_sio`; see Section 6.
- ttyUSB0 and ttyUSB4 (on hub `3-1.4.x`) belong to a different physical device.

---

## 3. Serial Port Details

| Port    | Function          | Baud   | Framing         |
|---------|-------------------|--------|-----------------|
| ttyUSB2 | Console / UART0   | 115200 | 8N1, no flow    |
| ttyUSB3 | UART1 / PL UART   | 115200 | 8N1, no flow    |
| ttyUSB5 | Spare / Platform  | 115200 | 8N1, no flow    |

Default baud: **115200**. Override with `UART_BAUD=<rate>` env var for scripts.

---

## 4. udev Permissions

Users need membership in:

| Group    | Purpose                       |
|----------|-------------------------------|
| dialout  | Serial port access (ttyUSB*)  |
| plugdev  | USB device access (libusb)    |

Recommended udev rule (`/etc/udev/rules.d/99-ft4232h-jtag.rules`):
```
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6011", \
    ATTRS{serial}=="XFL1OSWWFM2B", MODE="0666", GROUP="plugdev"
```

Apply with: `sudo udevadm control --reload-rules && sudo udevadm trigger`

---

## 5. Tool Availability Matrix

| Tool                       | Status    | Notes                                              |
|----------------------------|-----------|----------------------------------------------------|
| openFPGALoader             | CHECK     | `sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs` |
| openocd                    | CHECK     | Used as fallback when openFPGALoader unavailable   |
| vivado                     | CHECK     | Expected at `/home/ormastes/Xilinx/2025.2/Vivado/` |
| yosys                      | CHECK     | Open-source synthesis (optional)                   |
| riscv64-unknown-elf-gcc    | CHECK     | Bare-metal cross compiler (preferred)              |
| riscv64-linux-gnu-gcc      | CHECK     | Linux-target cross compiler (fallback)             |

Run `sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs` for live tool status.

---

## 6. JTAG Access Procedure

When `ftdi_sio` is loaded (default), all 4 FT4232H interfaces are claimed as serial ports.
Interface 0 (JTAG/MPSSE) must be freed before `openFPGALoader` or `openocd` can use it.

**Unbind for JTAG:**
```sh
sh scripts/fpga/jtag-ftdi-unbind.shs
```

**Rebind after programming:**
```sh
sh scripts/fpga/jtag-ftdi-unbind.shs --rebind
```

The `FTDI_USB_PATH` env var overrides the default `3-2:1.0` if the board appears on a different USB path.

---

## 7. Known Issues

### RV64-FPGA-001: ftdi_sio claims JTAG interface on connect

**Symptom:** `openFPGALoader -c ft4232 --detect` fails with `libusb_open() failed` or device busy.
**Root Cause:** Linux `ftdi_sio` driver auto-binds all 4 interfaces including Channel A (JTAG).
**Workaround:** Run `sh scripts/fpga/jtag-ftdi-unbind.shs` before any JTAG operation.
**Resolution:** Persistent udev rule with `DRIVER=="ftdi_sio", ATTRS{bInterfaceNumber}=="00", GOTO="ftdi_jtag_unbind"` (requires custom rule; not yet deployed).

### RV64-FPGA-002: Vivado not available in CI / headless environment

**Symptom:** `tool_vivado` reports FAIL in CI preflight.
**Root Cause:** Vivado is a proprietary tool, not installed in CI containers.
**Impact:** AC-5 (FPGA upload) is BLOCKED in CI; hardware-only test gate applies.
**Workaround:** Use `openFPGALoader` as the primary programming tool where possible; Vivado only required for full bitstream generation.

### RV64-FPGA-003: JTAG chain detection depends on bitstream loaded state

**Symptom:** `openFPGALoader --detect` may show empty chain if board is powered but no bitstream configured.
**Root Cause:** FT4232H responds on USB even when FPGA fabric is not configured.
**Workaround:** Pre-load a minimal bitstream or use `--cable ft4232` with explicit target device.

---

## 8. Build Artifact Locations

| Artifact          | Expected Path                          |
|-------------------|----------------------------------------|
| ELF (bare-metal)  | `build/riscv64-fpga/simpleos.elf`      |
| Raw binary        | `build/riscv64-fpga/simpleos.bin`      |
| FPGA bitstream    | `build/riscv64-fpga/simpleos.bit`      |
| Hardware manifest | `doc/08_tracking/hardware/hardware_manifest.sdn` |

Artifacts are generated by Agent D (bare-metal hello) and the platform capsule build.

---

## 9. Related Scripts

| Script                                        | Purpose                                |
|-----------------------------------------------|----------------------------------------|
| `scripts/check/check-riscv64-fpga-simpleos-preflight.shs` | Hardware preflight checks        |
| `scripts/fpga/jtag-ftdi-unbind.shs`                | Unbind/rebind JTAG interface from ftdi_sio |
| `scripts/check/check-kria-k26-fpga-bringup.shs`     | Reference pattern (Kria K26 variant)   |
