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

Apollo Lake also has a separate, proprietary Intel DCI USB 3.x DbC debug lane
when firmware/security gates, qualified cable, and Intel tooling are present.
It is not exposed through CN22. See `up_squared_apl_intel_dci_debug.md` for the
run-control, RAM-load, reset, and storage-programming analysis.

## Board-attached media and remote upload

The Type-A connectors are USB host ports; the Micro-B connector is OTG.
Connector presence does not make a Type-A-attached stick visible to another
computer. Prefer preparing the stick on the build host and returning it to
UP2. If UP2 already boots Linux from other media, SSH/SFTP may stage the image
on UP2, followed by a board-local, identity-gated write and exact-length
readback. Stage first; never stream SSH directly into a raw device.

The original firmware also supports Ethernet PXE. A small x64 UEFI Linux
environment can be loaded into RAM over an isolated DHCP/TFTP network and used
as the same board-local writer. This is a fallback, not proof that the current
firmware, NIC, DHCP, or SimpleOS network path is ready. UEFI Shell launches an
EFI application already on FAT media; it is not a general remote transfer
service. UART/XMODEM is not supplied by PC UEFI, and Linux USB gadget mode
requires a live UDC plus explicit gadget configuration.

The original board has soldered eMMC, SATA/mSATA, and an M.2 2230 E-key rather
than a general M-key NVMe socket. An NVMe SSD in a USB enclosure is exposed via
USB mass-storage/UAS-to-SCSI and must be identified by transport, stable
identity, serial, and capacity—not by assuming `/dev/nvme*`.

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
- Original specifications: https://up-board.org/upsquared/specifications/
- OpenSSH `scp`: https://man.openbsd.org/scp.1
- GNU `dd`: https://www.gnu.org/software/coreutils/manual/html_node/dd-invocation.html
- Linux `lsblk`: https://man7.org/linux/man-pages/man8/lsblk.8.html
- UEFI PXE:
  https://uefi.org/specs/UEFI/2.11/24_Network_Protocols_SNP_PXE_BIS.html
- Linux USB gadget/UDC:
  https://www.kernel.org/doc/html/latest/driver-api/usb/gadget.html
