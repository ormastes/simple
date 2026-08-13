<!-- codex-research -->
# StarFive VisionFive 2 SimpleOS — domain research

## Board and ISA

The likely target is the StarFive VisionFive 2, based on the JH7110 quad-core RV64GC SoC. Board revision must be checked from the silk screen; official SDK material uses `jh7110-visionfive-v2.dtb` for the common 1.2A/1.3B revisions.

Primary references:

- [VisionFive 2 introduction and CPU](https://doc-en.rvspace.org/VisionFive2/Datasheet/VisionFive_2/introduction_ds.html)
- [VisionFive 2 SDK boot guide and DTB](https://doc-en.rvspace.org/VisionFive2/SDK_Quick_Start_Guide/VisionFive2_SDK_QSG/booting_visionfive_2.html)

## Boot chain

The JH7110 BootROM loads SPL into SRAM at `0x08000000`. SPL initializes DDR and loads the firmware payload, normally OpenSBI plus U-Boot, to DDR. The documented QSPI layout places SPL at offset `0`, environment at `0xF0000`, and firmware payload at `0x100000`. A first SimpleOS port should use the established OpenSBI/U-Boot handoff rather than replace SPL/DDR initialization.

- [JH7110 BootROM flow](https://doc-en.rvspace.org/VisionFive2/Boot_UG/JH7110_SDK/bootrom.html)
- [Boot address allocation](https://doc-en.rvspace.org/VisionFive2/Boot_UG/JH7110_SDK/boot_address_allocation.html)
- [Boot-mode switch settings](https://doc-en.rvspace.org/VisionFive2/Quick_Start_Guide/VisionFive2_SDK_QSG/boot_mode_settings.html)

Boot-mode RGPIO1/RGPIO0 values are QSPI `00`, SD `01`, eMMC `10`, and UART recovery `11`. UART recovery is a recovery mechanism, not the normal kernel transport.

## UART

Official material maps UART0 TX/RX to GPIO5/GPIO6 and uses 115200 baud. JH7110 boot evidence identifies UART0 as a 16550A at MMIO `0x10000000` with a 1.5 MHz base baud. This happens to match the existing QEMU UART address, but the implementation must not infer clock, reset, pinmux, interrupt, register width, or divisor compatibility from that coincidence; those values must come from the active DTB/U-Boot contract.

Live DTB/MMIO evidence refines the generic 16550-compatible label: this board's
UART is DesignWare 8250-compatible and requires 32-bit register accesses with
register shift 2. Treating it as QEMU's byte-wide ns16550 loses output.

- [JH7110 board-level UART0 pin configuration](https://doc-en.rvspace.org/VisionFive2/DG_GPIO/JH7110_SDK/board_level_configuration.html)
- [VisionFive 2 serial console setup](https://doc-en.rvspace.org/VisionFive2/Quick_Start_Guide/VisionFive2_QSG/for_windows2%20-%20vf2.html)
- [JH7110 TRM UART register description](https://doc-en.rvspace.org/JH7110/TRM/JH7110_TRM/register_descript_uart.html)

## JTAG

Official JTAG guidance supports FreedomStudio or J-Link. The documented JH7110 scan example expects TAP ID `0x07110cfd`, five harts, and a GDB server on port 3333. Adapter identity and voltage must be proven before reset/halt/load commands are allowed.

- [VisionFive 2 JTAG overview](https://doc-en.rvspace.org/VisionFive2/FAQ/VisionFive_2/jtag_1.html)
- [JH7110 JTAG scan example](https://doc-en.rvspace.org/VisionFive2/FAQ/VisionFive_2/windows.html)

## Consequences for SimpleOS

1. Use U-Boot/OpenSBI to enter the existing S-mode kernel lane initially.
2. Pass and validate the board DTB instead of inheriting QEMU device constants.
3. Make UART output available before filesystem initialization, with bounded polling and visible failure markers.
4. Package or mount a deterministic root directory before launching the CLI; `ls` proof must show named entries, not merely a prompt.
5. Keep JTAG optional for normal boot but mandatory as a non-destructive diagnostic/load path when a supported probe is attached.

## Network observation

The only non-gateway LAN neighbor observed was `192.168.1.10` with MAC prefix `58:9c:fc`, registered to the FreeBSD Foundation rather than StarFive. StarFive's locally installed OUI database entry is `6c:cf:39`; therefore the neighbor is not affirmative VisionFive evidence and must not be used as the board target without an independent identity check.

## Tigard electrical prerequisites

Tigard uses FT2232H interface B for JTAG. Its mode switch must select SPI/JTAG. For a target-powered connection, VTGT is the target reference voltage and grounds must be common; Tigard must not be configured to source a conflicting voltage into an already powered target. An all-ones scan is not a valid JH7110 TAP identification. The expected JH7110 TAP ID remains `0x07110cfd`; accept the board identity only after that value (and the expected hart chain) is observed.

- [Tigard official repository, modes, power, and pinout](https://github.com/tigard-tools/tigard)
