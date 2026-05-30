# Artix-7 100T JTAG Detection Check

**Date:** 2026-04-30
**Status:** Partial success
**Board Model:** MiLianKe `MLK-S02-100T`
**Scope:** Physical FPGA reachability only, not bitstream programming or runtime proof

## Summary

A simple non-invasive `MLK-S02-100T` board check succeeded from this workspace:

- USB probe enumeration succeeded.
- `openFPGALoader` detected a live Xilinx Artix-7 100T device.
- OpenOCD also saw the same Xilinx IDCODE on JTAG.

This proves that the attached `MLK-S02-100T` FPGA is physically reachable over JTAG from this host.
It does **not** prove that the board-specific build/program/run flow is configured in the repo.

## Commands Run

```bash
lsusb
openFPGALoader --scan-usb
openFPGALoader --detect
openocd -c "adapter driver ftdi; transport select jtag; ftdi_vid_pid 0x0403 0x6010; init; scan_chain; shutdown"
```

## Observed Results

### USB enumeration

- Xilinx Platform Cable USB II present: `03fd:0008`
- FT2232-based JTAG interface present: `0403:6010`
- CH340 USB-UART present separately on the host as `/dev/ttyUSB0`

`openFPGALoader --scan-usb` identified:

- probe type: `FTDI2232`
- manufacturer: `Xilinx`
- serial: `2515B22F4DE`
- product: `MiLianKe.JTAG1U1`

Combined with the detected FPGA part and the CH340 UART bridge, this matches the known `MLK-S02-100T` hardware profile.

### FPGA detection

`openFPGALoader --detect` reported:

- manufacturer: `xilinx`
- family: `artix a7 100t`
- model: `xc7a100`
- IR length: `6`

### OpenOCD cross-check

OpenOCD also observed a Xilinx TAP with IDCODE:

- `0x13631093`

The OpenOCD check was not promoted into a usable target session because there is no board-specific TAP and target configuration in the repo for this board yet.

## What Succeeded

- host can see the FTDI/JTAG interface
- host can talk to the FPGA scan chain
- FPGA identity is stable across two tools

## What Did Not Happen

- no Vivado build was run
- no board-specific XDC was used
- no bitstream was programmed
- no UART or other runtime proof was observed
- no authoritative "example running on board" claim can be made yet

## Conclusion

The board passes a basic physical reachability test from this host.

Current confidence statement:
- **JTAG path works**
- **MLK-S02-100T device identity is consistent with host-observed hardware**
- **repo board support is still incomplete**

Next step for a real example run:
- identify the exact board model
- add board-specific part/XDC/build flow
- synthesize a trivial LED/UART design
- program it and capture runtime evidence
