# RISC-V 64 FPGA Hardware Inventory — 2026-05-19

**Board:** ML_Carrier_Card (Xilinx/AMD Kria K26 / XCZU5EV carrier)
**Date:** 2026-05-19
**Operator:** ormastes

---

## Live Refresh — 2026-07-19

The numbered sections below retain the 2026-05-19 inventory. Device numbers
such as `ttyUSB2` are historical and must not be used as stable identifiers.
The current read-only host snapshot is:

| Item | Current observation |
|---|---|
| Connected USB bridge | `0403:6011` FT4232H, serial `XFL1OSWWFM2B` |
| udev identity | `Xilinx_ML_Carrier_Card_XFL1OSWWFM2B` |
| Board lane | Kria K26/KV260 ML carrier |
| Other FPGA board | No `0403:6010` MLK-S02/Artix-7 bridge is connected |
| External PL UART | No non-Xilinx `/dev/serial/by-id` adapter is present |
| Network identity | No authoritative board neighbor or address is established |

Current stable serial links and driver ownership are:

| FTDI interface | Stable link | Driver state |
|---|---|---|
| `3-2:1.0` / if00 | `...XFL1OSWWFM2B-if00-port0` -> `ttyUSB0` | `ftdi_sio` |
| `3-2:1.1` / if01 | `...XFL1OSWWFM2B-if01-port0` -> `ttyUSB1` | `ftdi_sio` |
| `3-2:1.2` / if02 | missing | **unbound** |
| `3-2:1.3` / if03 | `...XFL1OSWWFM2B-if03-port0` -> `ttyUSB2` | `ftdi_sio` |

A read-only `openFPGALoader` channel probe detached interface 2; the probe was
stopped and no bitstream or board memory was written. A USB bridge reset did
not rebind it. Restore the interface by physically replugging the board USB
cable, or run:

```sh
printf '%s' '3-2:1.2' | sudo tee /sys/bus/usb/drivers/ftdi_sio/bind >/dev/null
```

Before a later JTAG operation, free interface 0 with the existing
`scripts/fpga/jtag-ftdi-unbind.shs` helper and rebind it afterward. Do not run
another channel scan. The merged FTDI ports are PS/transport interfaces; they
do not prove the generated tops' PL UART, which is routed to PMOD H12/E10.

Installed host tools are Vivado 2025.2, GHDL 4.1.0, Yosys 0.67, SBY 0.67,
OpenOCD 0.12.0, openFPGALoader 0.12.0, GCC 13.3.0
(`riscv64-linux-gnu`) and GCC 13.2.0 (`riscv64-unknown-elf`). There is no
RV32-named compiler executable. Vivado, `hw_server`, and XSDB are installed
under `/home/ormastes/Xilinx/2025.2/Vivado/bin`.

The ignored bitstream at
`/home/ormastes/dev/pub/simple/build/build/xilinx_kv260/gateware/xilinx_kv260.bit`
is 4,522,254 bytes, dated 2026-05-21, and has SHA-256
`e66263f73d2a23548f6011a1b6936eb11c2041ce8833cc83051517f047300887`.
It is stale external-core/marker evidence, not an authoritative F1/N3
Simple-compiled RV32/RV64 product or Linux login/`ls` artifact.

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
