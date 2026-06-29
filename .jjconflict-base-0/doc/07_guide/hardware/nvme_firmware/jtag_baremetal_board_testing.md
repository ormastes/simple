# Running on a baremetal board over JTAG (KV260)

The Simple-generated bare-metal binary (e.g. `build/os/simpleos_riscv32.elf`, the same artifact the
`nvme_rv32_baremetal_boot_spec` boots on QEMU) can be loaded and observed on a real **KV260
(Zynq UltraScale+ K26)** board over **JTAG**, using Xilinx `hw_server` + `xsdb` and the FT4232H
USB-JTAG/UART adapter. This is the baremetal-remote path; QEMU is the host-side equivalent.

## Verified operational on this host (2026-06-29)
`scripts/check/check-riscv64-fpga-simpleos-preflight.shs` was run on the physical board and reported
`preflight_complete=true` with:
- `PASS ft4232h_usb_present` — FT4232H JTAG/UART adapter `0403:6011` (KV260 ML Carrier Card) present
- `PASS serial_ports_present` — `/dev/ttyUSB0..3` + `/dev/serial/by-id/usb-Xilinx_ML_Carrier_Card_*`
- `PASS tool_openocd` (0.12.0), `PASS tool_vivado` (2025.2), `PASS tool_openfpgaloader`
- `PASS artifact_simpleos_elf` / `_bin` / `_bitstream` (the rv32 ELF + the 4.5 MB `.bit`)
- one prep step required: `FAIL jtag_interface_free` — the FT4232H JTAG channel is bound to the
  `ftdi_sio` kernel driver and must be unbound before JTAG use (this needs **root**).

## Mechanism (scripts/fpga/)
`hw_server` + `xsdb` reach the board over JTAG; a marker is written byte-by-byte over JTAG into the
ZynqMP **PS UART1** TX FIFO (`mwr 0xff010030`), and the same bytes are read back on the USB serial
console — so a test "runs on the board through JTAG" when its marker appears on serial. The
telnet-over-serial bridge (`scripts/fpga/telnet_serial_bridge.spl`) relays the console for remote
observation; the same harness validates a physical board or a QEMU `-serial`.

## Runbook
```bash
# 1. Free the JTAG channel from ftdi_sio (REQUIRES ROOT — the script self-sudos):
sh scripts/fpga/jtag-ftdi-unbind.shs            # --rebind to restore serial afterward
# 2. Run the end-to-end JTAG board test (programs the bitstream, injects a marker over JTAG,
#    observes it on serial via the telnet bridge, asserts marker_seen):
sh scripts/fpga/check_kv260_telnet_serial_system.shs
#    -> PASS when the captured serial contains TELNET_PROBE_STATUS=marker_seen
```

## Current scope / limitation
The JTAG path validates the **PS-UART transport** today (synthetic marker injected over JTAG, observed
on serial). Running the full RV softcore so it boots and emits its *own* test markers over the **PL**
UART is blocked on a 3.3 V PMOD (J2) UART adapter not currently fitted — see the header of
`scripts/fpga/check_kv260_telnet_serial_system.shs`. PS-side ARM testing and transport validation are
operational now.

## Note
The unbind and the live board run require **root** (no passwordless sudo in the automation account);
run them from an interactive shell. The host-side equivalent that needs no privilege is
`bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl` (boots the same
rv32 ELF on `qemu-system-riscv32`).
