# Domain research: UP Squared Apollo Lake boot and debug

Date: 2026-08-16

## Board and UART

The original UP Squared (`UPS-APL`) uses Intel Apollo Lake. The official fifth
edition manual defines CN16 as a ten-pin USB panel/header with 3.3 V TTL UART:
pin 8 ground, pin 9 UART RX, and pin 10 UART TX. Host and target TX/RX must be
crossed, with common ground. RS-232 voltage must not be applied.

Community evidence for the original board uses 115200 baud, 8 data bits, one
stop bit, no parity, and no hardware/software flow control; Linux commonly
names the board port `ttyS4`. Firmware output still depends on BIOS console
redirection being enabled, so silence is not proof of bad wiring.

## Safe boot/upload path

The x64 UEFI removable-media fallback is
`\EFI\BOOT\BOOTX64.EFI`. UP Squared firmware exposes a one-time boot-device
menu with F7 and setup with Delete. The safe first-light path is therefore a
dedicated removable FAT32/GPT USB stick selected for one boot, without changing
internal eMMC, SATA/NVMe, UEFI variables, or BIOS/SPI contents.

The existing repository image shape—GPT plus EF00 FAT32 ESP and a standalone
GRUB x64 EFI application embedding the multiboot kernel—matches that contract.
An offline structural check is necessary but cannot replace live firmware,
kernel, UART, filesystem, and shell evidence.

## Debug boundary

The official manual labels CN22 **CPLD and BIOS update**. It exposes JTAG plus
SPI signals and includes 1.8 V. It does not document an Apollo Lake CPU JTAG
debug chain. Tigard/OpenOCD must therefore not be attached or driven as a CPU
debugger on CN22. First bring-up uses UART logs and UEFI removable media;
hardware reset remains the physical power/reset path.

## Primary sources

- UP Squared UPS-APL User Manual, fifth edition:
  https://up-shop.org/media/productattach/u/p/up_squared_ups-apl_manual_5th_ed_0716c.pdf
- Slim Bootloader UP2 board notes (CN16 UART and Apollo Lake):
  https://slimbootloader.github.io/supported-hardware/up2.html
- Zephyr UP Squared board guide (UEFI USB boot and 115200 serial):
  https://docs.zephyrproject.org/latest/boards/up-bridge-the-gap/up_squared/doc/index.html
- UEFI 2.9A Boot Manager removable-media behavior:
  https://uefi.org/specs/UEFI/2.9_A/03_Boot_Manager.html
- UP Squared UEFI BIOS download instructions:
  https://downloads.up-community.org/download/up-squared-uefi-bios-v5-2/
