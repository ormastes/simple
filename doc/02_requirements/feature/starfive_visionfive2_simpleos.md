<!-- codex-research -->
# StarFive VisionFive 2 SimpleOS requirements

Selection: OpenSBI/U-Boot RAM-boot MVP, approved by the user on 2026-08-15.

## Requirements

- **REQ-001 — Named board target:** expose `riscv64-starfive-jh7110` as a first-class SimpleOS RV64GC board target without changing QEMU or FPGA board behavior.
- **REQ-002 — Firmware handoff:** build an ELF suitable for loading at `0x40200000` and entering in supervisor mode through the board's existing OpenSBI/U-Boot chain, with DTB address preserved for board discovery.
- **REQ-003 — Board console:** select the JH7110 DesignWare 8250 UART0 contract explicitly (MMIO `0x10000000`, 32-bit registers, shift 2, firmware-configured 115200 8N1) and emit deterministic entry, console-ready, filesystem-ready, and shell-ready markers.
- **REQ-004 — Deterministic root:** package and mount a read-only MVP root containing at least `/bin`, `/etc`, and `/README.txt` before starting the serial shell.
- **REQ-005 — Real CLI `ls`:** route `ls /` through the mounted VFS and display those packaged entries; hardcoded listing output is forbidden.
- **REQ-006 — Build receipt:** produce the ELF plus a manifest recording image hash, load/entry addresses, board target, DTB contract, compiler provenance, and build command.
- **REQ-007 — Safe board tooling:** provide Tigard UART capture and optional JTAG scan/load tooling that validates USB identity/channel mapping and fails closed on missing/ambiguous devices, all-ones scans, or unexpected TAP IDs.
- **REQ-008 — U-Boot load flow:** document and automate the non-flashing RAM-load/start commands; the normal flow must not alter QSPI, SPL, OpenSBI, or U-Boot.
- **REQ-009 — Diagnostic preservation:** capture UART/OpenOCD transcripts under a deterministic evidence directory and restore the FTDI kernel driver after JTAG operations.

## Exclusions

Native SD/eMMC, Ethernet, GPU, direct BootROM/SPL replacement, and persistent writable root support are outside this selected MVP.
